using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Roslyn.Compilers.CSharp;
using Roslyn.Compilers;

namespace FurtherTypeInferencing
{
    /// <summary>
    /// Replace the given anonymous type creation expressions with the equivalent named type
    /// creation expression.
    /// </summary>
    class AnonRewriter : SyntaxRewriter
    {
        private SemanticModel Model;
        private Compilation Comp;
        private NamedTypeSymbol Type;
        private TypeSyntax NewType;
        public AnonRewriter(NamedTypeSymbol type, SemanticModel model, Compilation comp, TypeSyntax newType)
        {
            Type = type;
            Model = model;
            Comp = comp;
            NewType = newType;
        }

        public override SyntaxNode VisitAnonymousObjectCreationExpression(AnonymousObjectCreationExpressionSyntax node)
        {
            var generated = node.Ancestors().OfType<ClassDeclarationSyntax>().Any(a => a.Identifier.ValueText.StartsWith("__FTI"));

            if (generated) return base.VisitAnonymousObjectCreationExpression(node);

            var expType = Model.GetTypeInfo(node).Type;

            if (AnonTypeUsage.AreEquivalent(expType, Type, Comp))
            {
                var propAssignment =
                    node.Initializers.OfType<AnonymousObjectMemberDeclaratorSyntax>()
                    .Select(
                    w =>
                    {
                        // Handle the new { Blah = Foo + Bar } case
                        if (w.NameEquals != null)
                        {
                            return
                                Syntax.BinaryExpression(
                                    SyntaxKind.AssignExpression,
                                    w.NameEquals.Identifier,
                                    w.Expression
                                ).WithLeadingTrivia(w.GetLeadingTrivia()).WithTrailingTrivia(w.GetTrailingTrivia());
                        }

                        // Handle the new { Fizz } case
                        return
                            Syntax.BinaryExpression(
                                SyntaxKind.AssignExpression,
                                w.Expression,
                                w.Expression
                            ).WithLeadingTrivia(w.GetLeadingTrivia()).WithTrailingTrivia(w.GetTrailingTrivia());
                    })
                    .Cast<ExpressionSyntax>().ToList();

                var separators = new List<SyntaxToken>();
                for (var i = 0; i < node.Initializers.SeparatorCount; i++) separators.Add(Syntax.Token(node.Initializers.GetSeparator(i).Kind));

                var equiv =
                    Syntax.ObjectCreationExpression(
                        NewType.WithLeadingTrivia(Syntax.ParseLeadingTrivia(" ")),
                        Syntax.ArgumentList(),
                        Syntax.InitializerExpression(
                            SyntaxKind.ObjectInitializerExpression,
                            Syntax.SeparatedList(
                                propAssignment,
                                separators
                            )
                        )
                    );

                return equiv.WithLeadingTrivia(node.GetLeadingTrivia()).WithTrailingTrivia(node.GetTrailingTrivia());
            }

            return base.VisitAnonymousObjectCreationExpression(node);
        }
    }

    /// <summary>
    /// Finds all the anoymous type creation expressions.
    /// </summary>
    class AnonTypeUsage : SyntaxWalker
    {
        public IEnumerable<AnonymousObjectCreationExpressionSyntax> Results { get; private set; }

        private SemanticModel Model;
        private Compilation Comp;
        private NamedTypeSymbol Type;
        public AnonTypeUsage(NamedTypeSymbol type, SemanticModel model, Compilation comp)
        {
            Type = type;
            Model = model;
            Comp = comp;
            Results = new List<AnonymousObjectCreationExpressionSyntax>();
        }

        internal static bool AreEquivalent(TypeSymbol a, TypeSymbol b, Compilation comp)
        {
            var aMembers = a.GetMembers().OfType<PropertySymbol>().ToList();
            var bMembers = b.GetMembers().OfType<PropertySymbol>().ToList();

            if (aMembers.Count != bMembers.Count) return false;

            for (var i = 0; i < aMembers.Count; i++)
            {
                var aMember = aMembers[i];
                var bMember = bMembers[i];

                if (aMember.Name != bMember.Name) return false;
                if (aMember.DeclaredAccessibility != bMember.DeclaredAccessibility) return false;


                var aType = aMember.Type;
                var bType = bMember.Type;

                var aName = aType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
                var bName = bType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);

                if (aName == bName) continue;

                var conv = comp.ClassifyConversion(aType, bType);

                if (!conv.IsIdentity) return false;
            }

            return true;
        }

        public override void VisitAnonymousObjectCreationExpression(AnonymousObjectCreationExpressionSyntax node)
        {
            var expType = Model.GetTypeInfo(node).Type;

            if (AreEquivalent(expType, Type, Comp))
            {
                ((List<AnonymousObjectCreationExpressionSyntax>)Results).Add(node);
            }

            base.VisitAnonymousObjectCreationExpression(node);
        }
    }

    /// <summary>
    /// Finds all method declarations.
    /// </summary>
    class GetMethodDecls : SyntaxWalker
    {
        public IEnumerable<MethodDeclarationSyntax> Results { get; private set; }

        public GetMethodDecls()
        {
            Results = new List<MethodDeclarationSyntax>();
        }

        public override void VisitMethodDeclaration(MethodDeclarationSyntax node)
        {
            ((List<MethodDeclarationSyntax>)Results).Add(node);

            base.VisitMethodDeclaration(node);
        }
    }

    /// <summary>
    /// Finds all return statements.
    /// </summary>
    class Returns : SyntaxWalker
    {
        public IEnumerable<ReturnStatementSyntax> Results { get; private set; }

        public Returns()
        {
            Results = new List<ReturnStatementSyntax>();
        }

        public override void VisitReturnStatement(ReturnStatementSyntax node)
        {
            ((List<ReturnStatementSyntax>)Results).Add(node);

            base.VisitReturnStatement(node);
        }
    }
}
