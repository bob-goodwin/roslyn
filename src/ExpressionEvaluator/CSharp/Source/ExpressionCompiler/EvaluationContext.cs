// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

#nullable enable

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Threading;
using Microsoft.CodeAnalysis.CodeGen;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.CSharp.Symbols.Metadata.PE;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Emit;
using Microsoft.CodeAnalysis.ExpressionEvaluator;
using Microsoft.CodeAnalysis.PooledObjects;
using Microsoft.DiaSymReader;
using Microsoft.VisualStudio.Debugger.Evaluation;
using Roslyn.Utilities;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
#pragma warning disable CS8600 // Possible null reference argument.
#pragma warning disable CS8601 // Possible null reference argument.
#pragma warning disable CS8602 // Possible null reference argument.
#pragma warning disable CS8604 // Possible null reference argument.
#pragma warning disable CS8603 // Possible null reference argument.

namespace Microsoft.CodeAnalysis.CSharp.ExpressionEvaluator
{
    internal sealed class EvaluationContext : EvaluationContextBase
    {
        private const string TypeName = "<>x";
        private const string MethodName = "<>m0";
        internal const bool IsLocalScopeEndInclusive = false;

        internal readonly MethodContextReuseConstraints? MethodContextReuseConstraints;
        internal readonly CSharpCompilation Compilation;

        private readonly MethodSymbol _currentFrame;
        private readonly MethodSymbol? _currentSourceMethod;
        private readonly ImmutableArray<LocalSymbol> _locals;
        private readonly ImmutableSortedSet<int> _inScopeHoistedLocalSlots;
        private readonly MethodDebugInfo<TypeSymbol, LocalSymbol> _methodDebugInfo;

        private EvaluationContext(
            MethodContextReuseConstraints? methodContextReuseConstraints,
            CSharpCompilation compilation,
            MethodSymbol currentFrame,
            MethodSymbol? currentSourceMethod,
            ImmutableArray<LocalSymbol> locals,
            ImmutableSortedSet<int> inScopeHoistedLocalSlots,
            MethodDebugInfo<TypeSymbol, LocalSymbol> methodDebugInfo)
        {
            RoslynDebug.AssertNotNull(inScopeHoistedLocalSlots);
            RoslynDebug.AssertNotNull(methodDebugInfo);

            MethodContextReuseConstraints = methodContextReuseConstraints;
            Compilation = compilation;
            _currentFrame = currentFrame;
            _currentSourceMethod = currentSourceMethod;
            _locals = locals;
            _inScopeHoistedLocalSlots = inScopeHoistedLocalSlots;
            _methodDebugInfo = methodDebugInfo;
        }

        /// <summary>
        /// Create a context for evaluating expressions at a type scope.
        /// </summary>
        /// <param name="compilation">Compilation.</param>
        /// <param name="moduleVersionId">Module containing type</param>
        /// <param name="typeToken">Type metadata token</param>
        /// <returns>Evaluation context</returns>
        /// <remarks>
        /// No locals since locals are associated with methods, not types.
        /// </remarks>
        internal static EvaluationContext CreateTypeContext(
            CSharpCompilation compilation,
            Guid moduleVersionId,
            int typeToken)
        {
            Debug.Assert(MetadataTokens.Handle(typeToken).Kind == HandleKind.TypeDefinition);

            var currentType = compilation.GetType(moduleVersionId, typeToken);
            RoslynDebug.Assert(currentType is object);
            var currentFrame = new SynthesizedContextMethodSymbol(currentType);
            return new EvaluationContext(
                null,
                compilation,
                currentFrame,
                currentSourceMethod: null,
                locals: default,
                inScopeHoistedLocalSlots: ImmutableSortedSet<int>.Empty,
                methodDebugInfo: MethodDebugInfo<TypeSymbol, LocalSymbol>.None);
        }

        /// <summary>
        /// Create a context for evaluating expressions within a method scope.
        /// </summary>
        /// <param name="metadataBlocks">Module metadata</param>
        /// <param name="symReader"><see cref="ISymUnmanagedReader"/> for PDB associated with <paramref name="moduleVersionId"/></param>
        /// <param name="moduleVersionId">Module containing method</param>
        /// <param name="methodToken">Method metadata token</param>
        /// <param name="methodVersion">Method version.</param>
        /// <param name="ilOffset">IL offset of instruction pointer in method</param>
        /// <param name="localSignatureToken">Method local signature token</param>
        /// <returns>Evaluation context</returns>
        internal static EvaluationContext CreateMethodContext(
            ImmutableArray<MetadataBlock> metadataBlocks,
            object symReader,
            Guid moduleVersionId,
            int methodToken,
            int methodVersion,
            uint ilOffset,
            int localSignatureToken)
        {
            var offset = NormalizeILOffset(ilOffset);

            var compilation = metadataBlocks.ToCompilation(moduleVersionId: default, MakeAssemblyReferencesKind.AllAssemblies);

            return CreateMethodContext(
                compilation,
                symReader,
                moduleVersionId,
                methodToken,
                methodVersion,
                offset,
                localSignatureToken);
        }

        /// <summary>
        /// Create a context for evaluating expressions within a method scope.
        /// </summary>
        /// <param name="compilation">Compilation.</param>
        /// <param name="symReader"><see cref="ISymUnmanagedReader"/> for PDB associated with <paramref name="moduleVersionId"/></param>
        /// <param name="moduleVersionId">Module containing method</param>
        /// <param name="methodToken">Method metadata token</param>
        /// <param name="methodVersion">Method version.</param>
        /// <param name="ilOffset">IL offset of instruction pointer in method</param>
        /// <param name="localSignatureToken">Method local signature token</param>
        /// <returns>Evaluation context</returns>
        internal static EvaluationContext CreateMethodContext(
            CSharpCompilation compilation,
            object? symReader,
            Guid moduleVersionId,
            int methodToken,
            int methodVersion,
            int ilOffset,
            int localSignatureToken)
        {
            var methodHandle = (MethodDefinitionHandle)MetadataTokens.Handle(methodToken);
            var currentSourceMethod = compilation.GetSourceMethod(moduleVersionId, methodHandle);
            var localSignatureHandle = (localSignatureToken != 0) ? (StandaloneSignatureHandle)MetadataTokens.Handle(localSignatureToken) : default;

            var currentFrame = compilation.GetMethod(moduleVersionId, methodHandle);
            RoslynDebug.AssertNotNull(currentFrame);
            var symbolProvider = new CSharpEESymbolProvider(compilation.SourceAssembly, (PEModuleSymbol)currentFrame.ContainingModule, currentFrame);

            var metadataDecoder = new MetadataDecoder((PEModuleSymbol)currentFrame.ContainingModule, currentFrame);
            var localInfo = metadataDecoder.GetLocalInfo(localSignatureHandle);

            var typedSymReader = (ISymUnmanagedReader3?)symReader;

            var debugInfo = MethodDebugInfo<TypeSymbol, LocalSymbol>.ReadMethodDebugInfo(typedSymReader, symbolProvider, methodToken, methodVersion, ilOffset, isVisualBasicMethod: false);

            var reuseSpan = debugInfo.ReuseSpan;
            var localsBuilder = ArrayBuilder<LocalSymbol>.GetInstance();
            MethodDebugInfo<TypeSymbol, LocalSymbol>.GetLocals(
                localsBuilder,
                symbolProvider,
                debugInfo.LocalVariableNames,
                localInfo,
                debugInfo.DynamicLocalMap,
                debugInfo.TupleLocalMap);

            var inScopeHoistedLocals = debugInfo.GetInScopeHoistedLocalIndices(ilOffset, ref reuseSpan);

            localsBuilder.AddRange(debugInfo.LocalConstants);

            return new EvaluationContext(
                new MethodContextReuseConstraints(moduleVersionId, methodToken, methodVersion, reuseSpan),
                compilation,
                currentFrame,
                currentSourceMethod,
                localsBuilder.ToImmutableAndFree(),
                inScopeHoistedLocals,
                debugInfo);
        }

        internal CompilationContext CreateCompilationContext()
        {
            return new CompilationContext(
                Compilation,
                _currentFrame,
                _currentSourceMethod,
                _locals,
                _inScopeHoistedLocalSlots,
                _methodDebugInfo);
        }

        /// <summary>
        /// Compile a collection of expressions at the same location. If all expressions
        /// compile successfully, a single assembly is returned along with the method
        /// tokens for the expression evaluation methods. If there are errors compiling
        /// any expression, null is returned along with the collection of error messages
        /// for all expressions.
        /// </summary>
        /// <remarks>
        /// Errors are returned as a single collection rather than grouped by expression
        /// since some errors (such as those detected during emit) are not easily
        /// attributed to a particular expression.
        /// </remarks>
        internal byte[]? CompileExpressions(
            ImmutableArray<string> expressions,
            out ImmutableArray<int> methodTokens,
            out ImmutableArray<string> errorMessages)
        {
            var diagnostics = DiagnosticBag.GetInstance();
            var syntaxNodes = expressions.SelectAsArray(expr => Parse(expr, treatAsExpression: true, diagnostics, out var formatSpecifiers));
            byte[]? assembly = null;
            if (!diagnostics.HasAnyErrors())
            {
                RoslynDebug.Assert(syntaxNodes.All(s => s != null));

                var context = CreateCompilationContext();
                if (context.TryCompileExpressions(syntaxNodes!, TypeName, MethodName, diagnostics, out var moduleBuilder))
                {
                    using var stream = new MemoryStream();

                    Cci.PeWriter.WritePeToStream(
                        new EmitContext(moduleBuilder, null, diagnostics, metadataOnly: false, includePrivateMembers: true),
                        context.MessageProvider,
                        () => stream,
                        getPortablePdbStreamOpt: null,
                        nativePdbWriterOpt: null,
                        pdbPathOpt: null,
                        metadataOnly: false,
                        isDeterministic: false,
                        emitTestCoverageData: false,
                        privateKeyOpt: null,
                        CancellationToken.None);

                    if (!diagnostics.HasAnyErrors())
                    {
                        assembly = stream.ToArray();
                    }
                }
            }

            if (assembly == null)
            {
                methodTokens = ImmutableArray<int>.Empty;
                errorMessages = ImmutableArray.CreateRange(
                    diagnostics.AsEnumerable().
                        Where(d => d.Severity == DiagnosticSeverity.Error).
                        Select(d => GetErrorMessage(d, CSharpDiagnosticFormatter.Instance, preferredUICulture: null)));
            }
            else
            {
                methodTokens = MetadataUtilities.GetSynthesizedMethods(assembly, MethodName);
                Debug.Assert(methodTokens.Length == expressions.Length);
                errorMessages = ImmutableArray<string>.Empty;
            }
            diagnostics.Free();
            return assembly;
        }

        internal override CompileResult? CompileExpression(
            string expr,
            DkmEvaluationFlags compilationFlags,
            ImmutableArray<Alias> aliases,
            DiagnosticBag diagnostics,
            out ResultProperties resultProperties,
            CompilationTestData? testData)
        {
            var syntax = Parse(expr, (compilationFlags & DkmEvaluationFlags.TreatAsExpression) != 0, diagnostics, out var formatSpecifiers);
            if (syntax == null)
            {
                resultProperties = default;
                return null;
            }

            syntax = new UplEvaluationTranslator(_currentFrame, syntax, _locals).Result as CSharpSyntaxNode;

            var context = CreateCompilationContext();
            if (!context.TryCompileExpression(syntax, TypeName, MethodName, aliases, testData, diagnostics, out var moduleBuilder, out var synthesizedMethod))
            {
                resultProperties = default;
                return null;
            }

            using var stream = new MemoryStream();

            Cci.PeWriter.WritePeToStream(
                new EmitContext(moduleBuilder, null, diagnostics, metadataOnly: false, includePrivateMembers: true),
                context.MessageProvider,
                () => stream,
                getPortablePdbStreamOpt: null,
                nativePdbWriterOpt: null,
                pdbPathOpt: null,
                metadataOnly: false,
                isDeterministic: false,
                emitTestCoverageData: false,
                privateKeyOpt: null,
                CancellationToken.None);

            if (diagnostics.HasAnyErrors())
            {
                resultProperties = default;
                return null;
            }

            Debug.Assert(synthesizedMethod.ContainingType.MetadataName == TypeName);
            Debug.Assert(synthesizedMethod.MetadataName == MethodName);

            resultProperties = synthesizedMethod.ResultProperties;
            return new CSharpCompileResult(
                stream.ToArray(),
                synthesizedMethod,
                formatSpecifiers: formatSpecifiers);
        }

        private static CSharpSyntaxNode? Parse(
            string expr,
            bool treatAsExpression,
            DiagnosticBag diagnostics,
            out ReadOnlyCollection<string>? formatSpecifiers)
        {
            if (!treatAsExpression)
            {
                // Try to parse as a statement. If that fails, parse as an expression.
                var statementDiagnostics = DiagnosticBag.GetInstance();
                var statementSyntax = expr.ParseStatement(statementDiagnostics);
                Debug.Assert((statementSyntax == null) || !statementDiagnostics.HasAnyErrors());
                statementDiagnostics.Free();
                var isExpressionStatement = statementSyntax.IsKind(SyntaxKind.ExpressionStatement);
                if (statementSyntax != null && !isExpressionStatement)
                {
                    formatSpecifiers = null;

                    if (statementSyntax.IsKind(SyntaxKind.LocalDeclarationStatement))
                    {
                        return statementSyntax;
                    }

                    diagnostics.Add(ErrorCode.ERR_ExpressionOrDeclarationExpected, Location.None);
                    return null;
                }
            }

            return expr.ParseExpression(diagnostics, allowFormatSpecifiers: true, out formatSpecifiers);
        }

        internal override CompileResult? CompileAssignment(
            string target,
            string expr,
            ImmutableArray<Alias> aliases,
            DiagnosticBag diagnostics,
            out ResultProperties resultProperties,
            CompilationTestData? testData)
        {
            var assignment = target.ParseAssignment(expr, diagnostics);
            if (assignment == null)
            {
                resultProperties = default;
                return null;
            }

            var context = CreateCompilationContext();
            if (!context.TryCompileAssignment(assignment, TypeName, MethodName, aliases, testData, diagnostics, out var moduleBuilder, out var synthesizedMethod))
            {
                resultProperties = default;
                return null;
            }

            using var stream = new MemoryStream();

            Cci.PeWriter.WritePeToStream(
                new EmitContext(moduleBuilder, null, diagnostics, metadataOnly: false, includePrivateMembers: true),
                context.MessageProvider,
                () => stream,
                getPortablePdbStreamOpt: null,
                nativePdbWriterOpt: null,
                pdbPathOpt: null,
                metadataOnly: false,
                isDeterministic: false,
                emitTestCoverageData: false,
                privateKeyOpt: null,
                CancellationToken.None);

            if (diagnostics.HasAnyErrors())
            {
                resultProperties = default;
                return null;
            }

            Debug.Assert(synthesizedMethod.ContainingType.MetadataName == TypeName);
            Debug.Assert(synthesizedMethod.MetadataName == MethodName);

            resultProperties = synthesizedMethod.ResultProperties;
            return new CSharpCompileResult(
                stream.ToArray(),
                synthesizedMethod,
                formatSpecifiers: null);
        }

        private static readonly ReadOnlyCollection<byte> s_emptyBytes =
            new ReadOnlyCollection<byte>(Array.Empty<byte>());

        internal override ReadOnlyCollection<byte> CompileGetLocals(
            ArrayBuilder<LocalAndMethod> locals,
            bool argumentsOnly,
            ImmutableArray<Alias> aliases,
            DiagnosticBag diagnostics,
            out string typeName,
            CompilationTestData? testData)
        {
            var context = CreateCompilationContext();
            var moduleBuilder = context.CompileGetLocals(TypeName, locals, argumentsOnly, aliases, testData, diagnostics);
            ReadOnlyCollection<byte>? assembly = null;

            if (moduleBuilder != null && locals.Count > 0)
            {
                using var stream = new MemoryStream();

                Cci.PeWriter.WritePeToStream(
                    new EmitContext(moduleBuilder, null, diagnostics, metadataOnly: false, includePrivateMembers: true),
                    context.MessageProvider,
                    () => stream,
                    getPortablePdbStreamOpt: null,
                    nativePdbWriterOpt: null,
                    pdbPathOpt: null,
                    metadataOnly: false,
                    isDeterministic: false,
                    emitTestCoverageData: false,
                    privateKeyOpt: null,
                    CancellationToken.None);

                if (!diagnostics.HasAnyErrors())
                {
                    assembly = new ReadOnlyCollection<byte>(stream.ToArray());
                }
            }

            if (assembly == null)
            {
                locals.Clear();
                assembly = s_emptyBytes;
            }

            typeName = TypeName;
            return assembly;
        }

        internal override bool HasDuplicateTypesOrAssemblies(Diagnostic diagnostic)
        {
            switch ((ErrorCode)diagnostic.Code)
            {
                case ErrorCode.ERR_DuplicateImport:
                case ErrorCode.ERR_DuplicateImportSimple:
                case ErrorCode.ERR_SameFullNameAggAgg:
                case ErrorCode.ERR_AmbigCall:
                    return true;
                default:
                    return false;
            }
        }

        internal override ImmutableArray<AssemblyIdentity> GetMissingAssemblyIdentities(Diagnostic diagnostic, AssemblyIdentity linqLibrary)
        {
            return GetMissingAssemblyIdentitiesHelper((ErrorCode)diagnostic.Code, diagnostic.Arguments, linqLibrary);
        }

        /// <remarks>
        /// Internal for testing.
        /// </remarks>
        internal static ImmutableArray<AssemblyIdentity> GetMissingAssemblyIdentitiesHelper(ErrorCode code, IReadOnlyList<object?> arguments, AssemblyIdentity linqLibrary)
        {
            RoslynDebug.AssertNotNull(linqLibrary);

            switch (code)
            {
                case ErrorCode.ERR_NoTypeDef:
                case ErrorCode.ERR_GlobalSingleTypeNameNotFoundFwd:
                case ErrorCode.ERR_DottedTypeNameNotFoundInNSFwd:
                case ErrorCode.ERR_SingleTypeNameNotFoundFwd:
                case ErrorCode.ERR_NameNotInContextPossibleMissingReference: // Probably can't happen.
                    foreach (var argument in arguments)
                    {
                        var identity = (argument as AssemblyIdentity) ?? (argument as AssemblySymbol)?.Identity;
                        if (identity != null && !identity.Equals(MissingCorLibrarySymbol.Instance.Identity))
                        {
                            return ImmutableArray.Create(identity);
                        }
                    }
                    break;

                case ErrorCode.ERR_DottedTypeNameNotFoundInNS:
                    if (arguments.Count == 2 &&
                        arguments[0] is string namespaceName &&
                        arguments[1] is NamespaceSymbol containingNamespace &&
                        containingNamespace.ConstituentNamespaces.Any(n => n.ContainingAssembly.Identity.IsWindowsAssemblyIdentity()))
                    {
                        // This is just a heuristic, but it has the advantage of being portable, particularly 
                        // across different versions of (desktop) windows.
                        var identity = new AssemblyIdentity($"{containingNamespace.ToDisplayString()}.{namespaceName}", contentType: System.Reflection.AssemblyContentType.WindowsRuntime);
                        return ImmutableArray.Create(identity);
                    }
                    break;

                case ErrorCode.ERR_NoSuchMemberOrExtension: // Commonly, but not always, caused by absence of System.Core.
                case ErrorCode.ERR_DynamicAttributeMissing:
                case ErrorCode.ERR_DynamicRequiredTypesMissing:
                // MSDN says these might come from System.Dynamic.Runtime
                case ErrorCode.ERR_QueryNoProviderStandard:
                case ErrorCode.ERR_ExtensionAttrNotFound: // Probably can't happen.
                    return ImmutableArray.Create(linqLibrary);

                case ErrorCode.ERR_BadAwaitArg_NeedSystem:
                    Debug.Assert(false, "Roslyn no longer produces ERR_BadAwaitArg_NeedSystem");
                    break;
            }

            return default;
        }

        internal class UplEvaluationTranslator : CSharpSyntaxRewriter
        {
            SyntaxNode node;
            public readonly SyntaxNode Result;
            SmallDictionary<string, string[]> mappings = new SmallDictionary<string, string[]>();
            ImmutableArray<LocalSymbol> locals;
            MethodSymbol methodSymbol;

            public UplEvaluationTranslator(MethodSymbol methodSymbol, SyntaxNode node, ImmutableArray<LocalSymbol> _locals)
            {
                GetMappings(methodSymbol);
                this.locals = _locals;
                this.node = node;
                this.methodSymbol = methodSymbol;

                if (mappings.Count() == 0)
                {
                    Result = node;
                }
                else
                {
                    Result = this.Visit(node);
                }
            }

            private bool IsTask(string[] matches)
            {
                if (matches.Length < 1) return false;
                return (matches[0].StartsWith("Task"));
            }
            private bool IsArray(string[] matches, out int size)
            {
                size = 0;
                if (matches.Length < 1) return false;
                int pos = matches[0].IndexOf('[');
                if (pos < 0) return false;
                return int.TryParse(matches[0].Substring(pos + 1, matches[0].Length - 2 - pos), out size);
            }

            public override SyntaxNode VisitMemberAccessExpression(MemberAccessExpressionSyntax node)
            {
                if (node.Name.Identifier.Text == "Result")
                {
                    var id = node.Expression as IdentifierNameSyntax;
                    if (id != null)
                    {
                        var x = IdentifierNameRewrite(id, out var isTask);
                        if (isTask) return x;
                    }

                    var ar = node.Expression as ElementAccessExpressionSyntax;
                    if (ar != null)
                    {
                        id = ar.Expression as IdentifierNameSyntax;
                        if (id != null)
                        {
                            var x = IdentifierNameRewrite(id, out var isTask);
                            if (isTask)
                            {
                                return SyntaxFactory.ElementAccessExpression(x as ExpressionSyntax, ar.ArgumentList);
                            }
                        }
                    }
                }

                return base.VisitMemberAccessExpression(node);
            }

            public override SyntaxNode VisitConditionalAccessExpression(ConditionalAccessExpressionSyntax node)
            {
                var binding = node.WhenNotNull as MemberBindingExpressionSyntax;
                if (binding != null)
                {
                    if (binding.Name.Identifier.Text == "Result")
                    {
                        var id = node.Expression as IdentifierNameSyntax;
                        if (id != null)
                        {
                            var x = IdentifierNameRewrite(id, out var isTask);
                            if (isTask) return x;
                        }

                        var ar = node.Expression as ElementAccessExpressionSyntax;
                        if (ar != null)
                        {
                            id = ar.Expression as IdentifierNameSyntax;
                            if (id != null)
                            {
                                var x = IdentifierNameRewrite(id, out var isTask);
                                if (isTask)
                                {
                                    return SyntaxFactory.ElementAccessExpression(x as ExpressionSyntax, ar.ArgumentList);
                                }
                            }
                        }
                    }
                }

                return base.VisitConditionalAccessExpression(node);
            }

            public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax node)
            {
                return IdentifierNameRewrite(node, out var result);
            }
            public SyntaxNode IdentifierNameRewrite(IdentifierNameSyntax node, out bool isTask)
            {
                isTask = false;
                var Name = node.Identifier.ValueText;
                if (mappings.TryGetValue(Name, out var matches))
                {
                    isTask = IsTask(matches);
                    if (IsArray(matches, out int arraySize))
                    {
                        string[] arrayvals = new string[arraySize];
                        string currentArray = null;
                        foreach (LocalSymbol local in locals)
                        {
                            if (local.Name != null)
                            {
                                int pos = local.Name.IndexOf("__I");
                                if (pos > 0)
                                {
                                    string arrayName = local.Name.Substring(0, pos);
                                    for (int i = 1; i < matches.Length; i++)
                                    {
                                        var m = matches[i];
                                        if (m == arrayName && (currentArray == null || currentArray == arrayName))
                                        {
                                            currentArray = arrayName;
                                            int pos2 = local.Name.IndexOf("__", pos + 1);
                                            string intStr = pos2 < 0 ? local.Name.Substring(pos + 3) : local.Name.Substring(pos + 3, pos2 - pos2 - 3);
                                            if (int.TryParse(intStr, out int index))
                                            {
                                                arrayvals[index] = local.Name;
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        if (currentArray != null)
                        {
                            SyntaxList<ArrayRankSpecifierSyntax> rankSpecifiers = new SyntaxList<ArrayRankSpecifierSyntax>()
                                .Add(ArrayRankSpecifier().AddSizes(OmittedArraySizeExpression()));
                            var arrayNode = ArrayCreationExpression(ArrayType(PredefinedType(Token(SyntaxKind.ObjectKeyword)), rankSpecifiers));
                            SeparatedSyntaxList<ExpressionSyntax> list = new SeparatedSyntaxList<ExpressionSyntax>();
                            int cnt = 0;
                            foreach (var arrayVal in arrayvals)
                            {
                                if (arrayVal != null)
                                {
                                    list = list.Add(IdentifierName(arrayVal));
                                }
                                else
                                {
                                    list = list.Add(LiteralExpression(SyntaxKind.StringLiteralExpression, Literal($"'{Name}[{cnt}]' is not in UPL scope.")));
                                }

                                cnt++;
                            }

                            arrayNode = arrayNode.WithInitializer(InitializerExpression(SyntaxKind.ArrayInitializerExpression, list));
                            return arrayNode;
                        }
                    }

                    foreach (LocalSymbol local in locals)
                    {
                        if (local.CanBeReferencedByName)
                        {
                            for (int i = 1; i < matches.Length; i++)
                            {
                                var m = matches[i];
                                if (m == local.Name)
                                {
                                    return IdentifierName(local.Name);
                                }
                            }
                        }
                    }

                    foreach (var param in this.methodSymbol.Parameters)
                    {
                        for (int i = 1; i < matches.Length; i++)
                        {
                            var m = matches[i];
                            if (m == param.Name)
                            {
                                return IdentifierName(param.Name);
                            }
                        }
                    }

                    return LiteralExpression(SyntaxKind.StringLiteralExpression, Literal($"'{Name}' is not in UPL scope."));
                }

                return node;
            }

            internal void GetMappings(MethodSymbol methodSymbol)
            {
                foreach (var attr in methodSymbol.GetAttributes())
                {
                    if (attr.AttributeClass.ToString() == "UPL.Xap.Internal.Symbol" && attr.ConstructorArguments.Count() == 1) 
                    {
                        var values = attr.ConstructorArguments.First().Values;
                        if (values.Length > 1)
                        {
                            int i = 0;
                            string[]? arr = null;
                            foreach (var s in values)
                            {
                                var name = s.Value as string;
                                if (i == 0)
                                {
                                    arr = new string[values.Length - 1];
                                    mappings[name] = arr;
                                }
                                else
                                {
                                    arr[i - 1] = name;
                                }

                                i++;
                            }
                        }
                    }
                }
            }
        }
    }
}
