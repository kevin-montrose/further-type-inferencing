using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Roslyn.Compilers;
using Roslyn.Compilers.CSharp;
using Roslyn.Services;
using Roslyn.Services.CSharp;
using System.IO;

namespace FurtherTypeInferencing
{
    /// <summary>
    /// Implements a re-writer for a whole csproj that enables the use of `var` as the declared return type
    /// of private and internal methods.
    /// 
    /// `var` is re-written to the "most restrictive" permissable type.
    /// </summary>
    class Program
    {
        private static bool Contains(Location haystack, Location needle)
        {
            return
                haystack.SourceTree.FilePath == needle.SourceTree.FilePath &&
                haystack.SourceSpan.Start <= needle.SourceSpan.Start &&
                haystack.SourceSpan.End >= needle.SourceSpan.End;
        }

        // Returns true if a is a subclass of b
        private static bool IsSubclass(TypeSymbol a, TypeSymbol b)
        {
            var @base = a.BaseType;

            while (@base != null)
            {
                if (@base == b) return true;

                @base = @base.BaseType;
            }

            return false;
        }

        /// <summary>
        /// Takes a set of types and returns the most "constrained" type that all of them can be converted to.
        /// 
        /// Worst case, it returns a TypeSyntax for `object`.
        /// 
        /// If the appropriate type is an anonymous one, `replaceType` contains a Tuple of that anonymous type and the 
        /// name of a new one that should be created to take its place.
        /// </summary>
        private static TypeSyntax FindCommonType(IEnumerable<TypeInfo> info, Compilation comp, out Tuple<NamedTypeSymbol, string> replaceType)
        {
            if (info.Any(a => a.Equals(TypeInfo.None)))
            {
                replaceType = null;
                return null;
            }

            var allPossibilities = info.SelectMany(i => i.Type.AllInterfaces).OfType<NamedTypeSymbol>().ToList();

            allPossibilities.AddRange(info.Select(s => s.Type).OfType<NamedTypeSymbol>());

            foreach (var i in info)
            {
                var @base = i.Type.BaseType;
                while (@base != null)
                {
                    allPossibilities.Add(@base);
                    @base = @base.BaseType;
                }
            }

            // Order so that subclasses are before superclasses, classes are before interfaces,
            //   special interfaces first, and generic types are before non-generic ones
            //   with the special case that System.Object is always the *last* option
            //   uses type name as a tie-breaker for ordering
            //
            // Special interfaces are anything that gets special treatment in the language, which for now is IEnumerable<T> and IEnumerable
            allPossibilities.Sort(
                (a, b) =>
                {
                    var aIsNotObject = a.TypeKind != TypeKind.Class || a.BaseType != null;
                    var bIsNotObject = b.TypeKind != TypeKind.Class || b.BaseType != null;

                    var aIsNotInterface = a.TypeKind != TypeKind.Interface;
                    var bIsNotInferface = b.TypeKind != TypeKind.Interface;

                    // Get both IEnumerable && IEnumerable<T>
                    var aIsSpecial = a.Name == "IEnumerable";
                    var bIsSpecial = b.Name == "IEnumerable";

                    var aIsSubclassOfB = IsSubclass(a, b);
                    var bIsSubclassOfA = IsSubclass(b, a);

                    if (aIsNotObject && !bIsNotObject) return -1;
                    if (bIsNotObject && !aIsNotObject) return 1;

                    if (aIsSubclassOfB) return -1;
                    if (bIsSubclassOfA) return 1;

                    if (aIsNotInterface && !bIsNotInferface) return -1;
                    if (bIsNotInferface && !aIsNotInterface) return 1;

                    if (!aIsNotInterface && !bIsNotInferface)
                    {
                        if (aIsSpecial && !bIsSpecial) return -1;
                        if (bIsSpecial && !aIsSpecial) return 1;
                    }

                    if (a.IsGenericType && !b.IsGenericType) return -1;
                    if (b.IsGenericType && !a.IsGenericType) return 1;

                    return a.MetadataName.CompareTo(b.MetadataName);
                }
            );

            var commonType = 
                allPossibilities.First(
                    t =>
                    {
                        var conversions = info.Select(a => comp.ClassifyConversion(a.Type, t)).ToList();

                        return conversions.All(a => a.Exists && a.IsImplicit);
                    }
                );

            string fullName;

            // we actually need to *replace* this type so we can put it in the returns
            if (commonType.IsAnonymousType)
            {
                fullName = "__FTI" + Guid.NewGuid().ToString().Replace("-", "");
                replaceType = Tuple.Create(commonType, fullName);
            }
            else
            {
                fullName = commonType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
                replaceType = null;
            }

            return Syntax.ParseTypeName(fullName);
        }

        /// <summary>
        /// Tries to rewrite the given method (with a var return type) so that it's declared return is actually valid C#.
        /// 
        /// Returns the replacemnt node, and set's replacementType if a new equivalent type with the given name needs to be created.
        /// </summary>
        private static SyntaxNode TryRewrite(MethodDeclarationSyntax method, SemanticModel model, Compilation comp, out Tuple<NamedTypeSymbol, string> replaceType)
        {
            var getReturns = new Returns();
            getReturns.Visit(method);
            var returns = getReturns.Results.ToList();

            var types = new List<TypeInfo>();

            foreach (var ret in returns)
            {
                var exp = ret.Expression;

                if (exp == null)
                {
                    types.Add(TypeInfo.None);
                    continue;
                }

                var type = model.GetTypeInfo(exp);

                types.Add(type);
            }

            var commonType = FindCommonType(types, comp, out replaceType);

            // void
            if (commonType == null)
            {
                commonType = Syntax.ParseTypeName("void");
            }

            commonType = commonType.WithLeadingTrivia(method.ReturnType.GetLeadingTrivia());
            commonType = commonType.WithTrailingTrivia(method.ReturnType.GetTrailingTrivia());

            return method.WithReturnType(commonType);
        }

        /// <summary>
        /// Adds a new internal class with the given name equivalent to the passed type to the given syntax tree.
        /// 
        /// Sets `created` to a reference to the newly created type.
        /// </summary>
        private static SyntaxNode AddType(NamedTypeSymbol equivTo, string withName, SyntaxNode tree, out TypeSyntax created)
        {
            created = Syntax.ParseTypeName(withName);

            var members =
                equivTo.GetMembers()
                .OfType<PropertySymbol>()
                .Select(
                    s => 
                    {
                        var prop = 
                            Syntax.PropertyDeclaration(
                                null,
                                Syntax.TokenList(Syntax.ParseToken("public")),
                                Syntax.ParseTypeName(s.Type.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat)).WithLeadingTrivia(Syntax.ParseLeadingTrivia(" ")).WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                                null,
                                Syntax.Identifier(s.Name),
                                Syntax.AccessorList(
                                    Syntax.List(
                                        Syntax.AccessorDeclaration(
                                            SyntaxKind.GetAccessorDeclaration,
                                            null, 
                                            Syntax.TokenList(), 
                                            Syntax.ParseToken("get"), 
                                            null,
                                            Syntax.ParseToken(";")
                                        ),
                                        Syntax.AccessorDeclaration(
                                            SyntaxKind.SetAccessorDeclaration,
                                            null,
                                            Syntax.TokenList(),
                                            Syntax.ParseToken("set"),
                                            null,
                                            Syntax.ParseToken(";")
                                        )
                                    )
                                )
                            );

                        return prop;
                    }
                )
                .Cast<MemberDeclarationSyntax>().ToList();

            var separators = new List<SyntaxToken>();
            for(var i = 0; i < members.Count - 1; i++) separators.Add(Syntax.ParseToken(","));

            var obj =
                Syntax.AnonymousObjectCreationExpression(
                    Syntax.SeparatedList(
                        equivTo.GetMembers()
                        .OfType<PropertySymbol>()
                        .Select(
                            p => 
                            {
                                var exp = Syntax.IdentifierName(p.Name);
                                return Syntax.AnonymousObjectMemberDeclarator(exp);
                            }
                        ),
                        separators
                    )
                ).WithLeadingTrivia(Syntax.ParseLeadingTrivia(" "));

            // Build the ToString() method that anonymous types have to have
            var toStringRef = Syntax.MemberAccessExpression(SyntaxKind.MemberAccessExpression, obj, Syntax.ParseToken("."), Syntax.IdentifierName("ToString"));
            var toStringAccess = Syntax.InvocationExpression(toStringRef);
            var toStringRet = Syntax.ReturnStatement(toStringAccess);
            var toStringStatements = Syntax.List<StatementSyntax>(toStringRet);
            var toStringBody =
                Syntax.Block(
                    Syntax.ParseToken("{"),
                    toStringStatements,
                    Syntax.ParseToken("}")
                );
            var toString =
                Syntax.MethodDeclaration(
                    null,
                    Syntax.TokenList(Syntax.ParseToken("public").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")), Syntax.ParseToken("override").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" "))),
                    Syntax.ParseTypeName("string").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    null,
                    Syntax.Identifier("ToString"),
                    null,
                    Syntax.ParameterList(),
                    null,
                    toStringBody
                );
            members.Add(toString);

            // Adding GetHashCode override anonymous types must have
            var hashCodeRef = Syntax.MemberAccessExpression(SyntaxKind.MemberAccessExpression, obj, Syntax.ParseToken("."), Syntax.IdentifierName("GetHashCode"));
            var hashCodeAccess = Syntax.InvocationExpression(hashCodeRef);
            var hashCodeRet = Syntax.ReturnStatement(hashCodeAccess);
            var hashCodeStatements = Syntax.List<StatementSyntax>(hashCodeRet);
            var hashCodeBody =
                Syntax.Block(
                    Syntax.ParseToken("{"),
                    hashCodeStatements,
                    Syntax.ParseToken("}")
                );
            var hashCode =
                Syntax.MethodDeclaration(
                    null,
                    Syntax.TokenList(Syntax.ParseToken("public").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")), Syntax.ParseToken("override").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" "))),
                    Syntax.ParseTypeName("int").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    null,
                    Syntax.Identifier("GetHashCode"),
                    null,
                    Syntax.ParameterList(),
                    null,
                    hashCodeBody
                );
            members.Add(hashCode);

            // Adding Equals method anonymous types must have
            var equalsAs = Syntax.ParseExpression("o as " + withName);
            var equalsAssign =
                Syntax.VariableDeclaration(
                    created.WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    Syntax.SeparatedList(
                        Syntax.VariableDeclarator(
                            Syntax.Identifier("other"),
                            null,
                            Syntax.EqualsValueClause(equalsAs)
                        )
                    )
                );
            var equalsEqualsRef = Syntax.MemberAccessExpression(SyntaxKind.MemberAccessExpression, obj, Syntax.ParseToken("."), Syntax.IdentifierName("Equals"));
            var equalsAccess = Syntax.InvocationExpression(equalsEqualsRef, Syntax.ArgumentList(Syntax.SeparatedList(Syntax.Argument(Syntax.ParseExpression("o")))));
            var equalsIf =
                Syntax.IfStatement(
                    Syntax.ParseExpression("other == null"),
                    Syntax.ReturnStatement(equalsAccess)
                );
            var equalsEqualsExps =
                equivTo.GetMembers()
                .OfType<PropertySymbol>()
                .Select(
                    p =>
                    {
                        var n = p.Name;
                        ExpressionSyntax ret;

                        if (p.Type.IsReferenceType)
                        {
                            var strExp = "(" + n + " != null ? " + n + ".Equals(other." + n + ") : (other." + n + " != null ? other." + n + ".Equals(" + n + ") : true ))";

                            ret = Syntax.ParseExpression(strExp);
                        }
                        else
                        {
                            ret = Syntax.ParseExpression(n + " == other." + n);
                        }

                        return ret.WithLeadingTrivia(Syntax.ParseLeadingTrivia(" ")).WithTrailingTrivia(Syntax.ParseTrailingTrivia(" "));
                    }
                ).ToList();
            ExpressionSyntax equalsBinary = equalsEqualsExps.First();
            for (var i = 1; i < equalsEqualsExps.Count; i++) equalsBinary = Syntax.BinaryExpression(SyntaxKind.LogicalAndExpression, equalsBinary, equalsEqualsExps[i]);
            var equalsBinaryRet = Syntax.ReturnStatement(equalsBinary.WithLeadingTrivia(Syntax.ParseLeadingTrivia(" ")));
            var equalsStatements =
                Syntax.List(
                    (StatementSyntax)Syntax.LocalDeclarationStatement(equalsAssign),
                    (StatementSyntax)equalsIf,
                    (StatementSyntax)equalsBinaryRet
                );
            var equalsBody =
                Syntax.Block(
                    Syntax.ParseToken("{"),
                    equalsStatements,
                    Syntax.ParseToken("}")
                );
            var equals =
                Syntax.MethodDeclaration(
                    null,
                    Syntax.TokenList(Syntax.ParseToken("public").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")), Syntax.ParseToken("override").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" "))),
                    Syntax.ParseTypeName("bool").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    null,
                    Syntax.Identifier("Equals"),
                    null,
                    Syntax.ParameterList(
                        Syntax.SeparatedList(
                            Syntax.Parameter(
                                null, 
                                Syntax.TokenList(), 
                                Syntax.ParseTypeName("object").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")), 
                                Syntax.Identifier("o"), 
                                null
                            )
                        )
                    ),
                    null,
                    equalsBody
                );
            members.Add(equals);

            var equiv =
                Syntax.ClassDeclaration(
                    null,
                    Syntax.ParseToken("internal").WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    Syntax.Identifier(withName).WithLeadingTrivia(Syntax.ParseLeadingTrivia(" ")).WithTrailingTrivia(Syntax.ParseTrailingTrivia(" ")),
                    null,
                    null,
                    null,
                    Syntax.List<MemberDeclarationSyntax>(members)
                );

            var namespaces = tree.ChildNodes().OfType<NamespaceDeclarationSyntax>();

            if (namespaces.Count() == 0 || namespaces.Count() > 1)
            {
                // HACK, better way to insert classes should be considered
                throw new Exception("Making some assumptions about namespaces, you can only have 1");
            }

            var @namespace = namespaces.Single();

            var updated = 
                @namespace.WithMembers(
                    @namespace.Members.Add(equiv)
                );

            return tree.ReplaceNode(@namespace, updated);
        }

        /// <summary>
        /// Replaces the given types in the given trees with references to new named types.
        /// 
        /// This is used for anonymous type hoisting where needed.
        /// </summary>
        private static Dictionary<string, SyntaxTree> HandleTypeReplacements(Dictionary<string, SyntaxTree> trees, IEnumerable<MetadataReference> references, List<Tuple<NamedTypeSymbol, string>> typeReplacements)
        {
            var comp = Compilation.Create("HandleTypeReplacements");
            comp = comp.AddReferences(references);
            comp = comp.AddSyntaxTrees(trees.Select(s => s.Value));

            var rewrittenTrees = trees;
            foreach (var replace in typeReplacements)
            {
                var added = false;
                TypeSyntax typeRef = null;

                foreach (var key in trees.Keys.ToList())
                {
                    var tree = rewrittenTrees[key];
                    var usage = new AnonTypeUsage(replace.Item1, comp.GetSemanticModel(tree), comp);
                    usage.Visit(tree.GetRoot());

                    var rewritten = tree.GetRoot();
                    if (usage.Results.Count() > 0)
                    {
                        if (!added)
                        {
                            rewritten = AddType(replace.Item1, replace.Item2, rewritten, out typeRef);
                            tree = SyntaxTree.Create(key, (CompilationUnitSyntax)rewritten);
                            rewritten = tree.GetRoot();
                            rewrittenTrees[key] = tree;
                            added = true;
                        }

                        var rewriteComp = Compilation.Create("HandleTypeReplacements2");
                        rewriteComp = rewriteComp.AddReferences(references);
                        rewriteComp = rewriteComp.AddSyntaxTrees(rewrittenTrees.Select(s => s.Value));

                        var changeRefs = new AnonRewriter(replace.Item1, rewriteComp.GetSemanticModel(tree), rewriteComp, typeRef);
                        rewritten = changeRefs.Visit(rewritten);
                    }

                    rewrittenTrees[key] = SyntaxTree.Create(key, (CompilationUnitSyntax)rewritten);
                }
            }

            return rewrittenTrees;
        }

        /// <summary>
        /// Runs one pass attempting to re-write the given syntax trees so that `var` no longer appears in the return
        /// types of methods.
        /// 
        /// Sets `didReplace` if any re-writing was successful.  If `didReplace` is false, subsequent calls to this method
        /// can be assumed to be no-ops.
        /// </summary>
        private static Dictionary<string, SyntaxTree> InferencePass(Dictionary<string, SyntaxTree> trees, IEnumerable<MetadataReference> references, out bool didReplace)
        {
            didReplace = false;

            var newTrees = new Dictionary<string, SyntaxTree>();

            var comp = Compilation.Create("InferencePass");
            comp = comp.AddReferences(references);
            comp = comp.AddSyntaxTrees(trees.Select(s => s.Value));

            var outerDiag = comp.GetDiagnostics();

            var rewrittenTrees = new Dictionary<string, SyntaxTree>();
            var typeReplacements = new List<Tuple<NamedTypeSymbol, string>>();

            foreach (var kv in trees)
            {
                var root = kv.Value.GetRoot();
                var model = comp.GetSemanticModel(kv.Value);
                var diag = model.GetDiagnostics();

                var getMethodDecls = new GetMethodDecls();
                getMethodDecls.Visit(root);
                var methodDecls = getMethodDecls.Results.ToList();

                var bins = root.DescendantNodes().OfType<BinaryExpressionSyntax>().ToList();

                var eligibleMethods =
                    methodDecls.Where(
                        m =>
                        {
                            var mods = m.Modifiers;

                            var isPublic = mods.Any(a => a.Value.ToString() == "public");
                            var isProtected = mods.Any(a => a.Value.ToString() == "protected");

                            return !isPublic && !isProtected;
                        }
                    ).ToList();

                // This is mighty convenient, Roslyn giving you sensical stuff in the face of "errors" is quite handy
                var needsInferencing = eligibleMethods.Where(w => (w.ReturnType is IdentifierNameSyntax) && ((IdentifierNameSyntax)w.ReturnType).IsVar).ToList();

                foreach (var infer in needsInferencing)
                {
                    Tuple<NamedTypeSymbol, string> replaceType;
                    var rewritten = TryRewrite(infer, model, comp, out replaceType);

                    if (rewritten != null)
                    {
                        root = root.ReplaceNode(infer, rewritten);

                        if (replaceType != null)
                        {
                            typeReplacements.Add(replaceType);
                        }

                        didReplace = true;
                        break;
                    }
                }

                rewrittenTrees[kv.Key] = SyntaxTree.Create(kv.Value.FilePath, (CompilationUnitSyntax)root);
            }

            rewrittenTrees = HandleTypeReplacements(rewrittenTrees, references, typeReplacements);

            return rewrittenTrees;
        }

        static int Main(string[] args)
        {
            if (args.Length != 2)
            {
                Console.WriteLine("Expected <solution file> <output directory> as parameters");
                return -1;
            }

            var sln = args[0];
            var outDir = args[1];

            if (!File.Exists(sln))
            {
                Console.WriteLine("Could not find <" + sln + ">");
                return -1;
            }

            if (!Directory.Exists(outDir))
            {
                Console.WriteLine("<" + outDir + "> doesn't exist");
                return -1;
            }

            var workspace = Workspace.LoadSolution(sln);

            if (workspace.CurrentSolution.Projects.Count() > 1)
            {
                Console.Write("As a demonstration, this only functions on the first project (alphabetically) in a solution");
            }

            var project = workspace.CurrentSolution.Projects.OrderBy(o => o.Name).First();

            Console.WriteLine("Converting project: " + project.Name);

            var references = project.MetadataReferences.ToList();
            var files = project.Documents.Where(w => w.FilePath.EndsWith(".cs")).Select(s => s.FilePath).ToList();

            var dir = Directory.GetParent(sln);

            var trees =
                files.ToDictionary(
                    csFile => csFile,
                    delegate(string csFile)
                    {
                        var code = File.ReadAllText(Path.Combine(dir.FullName, csFile));

                        return SyntaxTree.ParseCompilationUnit(code);
                    }
                );

            Dictionary<string, SyntaxTree> rewrittenTrees = trees;
            var goAgain = true;
            while (goAgain)
            {
                goAgain = false;
                rewrittenTrees = InferencePass(rewrittenTrees, references, out goAgain);
            }

            foreach (var file in rewrittenTrees)
            {
                var projDir = Path.GetDirectoryName(project.FilePath);
                var fileName = file.Key.Replace(projDir + Path.DirectorySeparatorChar, "");

                var outfile = Path.Combine(outDir, fileName);

                if (!Directory.GetParent(outfile).Exists)
                {
                    Directory.CreateDirectory(Directory.GetParent(outfile).FullName);
                }

                using (var stream = new StreamWriter(File.Create(outfile)))
                {
                    file.Value.GetRoot().WriteTo(stream);
                }
            }

            // Move the project file
            File.Copy(project.FilePath, Path.Combine(outDir, Path.GetFileName(project.FilePath)), overwrite: true);

            return 0;
        }
    }
}
