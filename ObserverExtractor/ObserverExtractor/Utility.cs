using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Symbols;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;
using System.Diagnostics;
using Microsoft.CodeAnalysis.Formatting;
using Microsoft.CodeAnalysis.MSBuild;
using Microsoft.CodeAnalysis.Editing;
using System.Text.RegularExpressions;

namespace ObserverTypeExtractor
{
    class Utility
    {
        MSBuildWorkspace workspace;
        Solution solution;
        
        Project targetProject;

        public Utility(string sln, string testProjectName)
        {
            Debug.Assert(File.Exists(sln));
            this.workspace = MSBuildWorkspace.Create();
            this.solution = workspace.OpenSolutionAsync(sln).Result;
            Debug.Assert(this.solution != null, "cannot retrive solution object type");

            this.targetProject = findProjectByName(testProjectName);
            Debug.Assert(this.targetProject != null, "cannot retrive project object type");

            
        }
        public List<Tuple<string, string>> ObserverMethodsExtractionInClassForDaikon(string testFileName, string PUTName)
        {
            List<Tuple<string, string>> observerMethods = new List<Tuple<string, string>>();
            List<Tuple<string, string>> varTypePairs = new List<Tuple<string, string>>();

            Document testClassDocument = FindDocumentByName(testFileName);

            /**** DEBUG ****/
            Debug.Assert(testClassDocument != null, "testClassDocument is null --- either it doesnt exists or cannot be found");

            DocumentEditor testClassEditor = DocumentEditor.CreateAsync(testClassDocument).Result;
            SyntaxTree testClassTree = testClassDocument.GetSyntaxTreeAsync().Result;
            SyntaxNode testClassRoot = testClassTree.GetRoot();

            
            var options = new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary);
            IReadOnlyList<MetadataReference> referencesForCompilation = this.targetProject.MetadataReferences;

            //Compile -> Get Semantic model -> get type info later on
            CSharpCompilation compilation = CSharpCompilation.Create("ArrayListTest")
                                           .AddReferences(referencesForCompilation)
                                           .AddSyntaxTrees(testClassTree)
                                           .WithOptions(options);

            SemanticModel model = compilation.GetSemanticModel(testClassTree);
            var results = compilation.GetSymbolsWithName(sym => true);
            var fieldSymbols = results.OfType<IFieldSymbol>().ToList<ISymbol>();
            foreach (IFieldSymbol field in fieldSymbols)
            {
               

                string identifier = field.Name;
                string typeStr = field.Type.ToString();

                observerMethods.Add(new Tuple<string, string>(identifier, typeStr));

            }

            return observerMethods;
        }

            public List<Tuple<string, string>> ObserverMethodsExtractionForDaikon(string testFileName, string PUTName)
        {
            List<Tuple<string, string>> observerMethods = new List<Tuple<string, string>>();
            List<Tuple<string, string>> varTypePairs = new List<Tuple<string, string>>();

            Document testClassDocument = FindDocumentByName(testFileName);

            /**** DEBUG ****/
            Debug.Assert(testClassDocument != null, "testClassDocument is null --- either it doesnt exists or cannot be found");

            DocumentEditor testClassEditor = DocumentEditor.CreateAsync(testClassDocument).Result;
            SyntaxTree testClassTree = testClassDocument.GetSyntaxTreeAsync().Result;
            SyntaxNode testClassRoot = testClassTree.GetRoot();

            Debug.Assert(testClassTree != null, "assume input tree is not null");
            IReadOnlyList<MetadataReference> referencesForCompilation = this.targetProject.MetadataReferences;

            
            SemanticModel model = getSemanticModel(testClassTree);

            // Find target method
            List<MethodDeclarationSyntax> testClassMethods = testClassRoot.DescendantNodes().OfType<MethodDeclarationSyntax>().ToList();
            int targetMethodIdx = FindMethodSyntaxIdxByName(testClassMethods, PUTName);
            MethodDeclarationSyntax targetMethod = testClassMethods[targetMethodIdx];

            //Get parameters of target method
            List<ParameterSyntax> parameters = targetMethod.ParameterList.Parameters.ToList();

            string pexVarName = "";
            foreach (ParameterSyntax p in parameters)
            {
                if (p.ToString().Contains("[PexAssumeUnderTest]"))
                {
                    pexVarName = p.Identifier.ToString();
                }

                varTypePairs.Add(new Tuple<string, string>(p.Identifier.ToString(), p.Type.ToString()));
            }
            // Debug.Assert(pexVarName != "");
            if (pexVarName == "")
            {
                Console.WriteLine("[INFO] There are no [PexAssumeUnderTest] in the arguments!");
            }

            // get body
            BlockSyntax body = targetMethod.Body;
            
            List<AssignmentExpressionSyntax> assignNodes = body.DescendantNodes().OfType<AssignmentExpressionSyntax>().ToList();

            foreach (AssignmentExpressionSyntax assExprNode in assignNodes)
            {
                IdentifierNameSyntax left = (IdentifierNameSyntax)assExprNode.Left;
                if (left == null) continue;

                Microsoft.CodeAnalysis.TypeInfo typeInfo = model.GetTypeInfo(left);
                
                string typeStr = typeInfo.Type.ToString();
                string identifier = left.Identifier.ToString();
                varTypePairs.Add(new Tuple<string, string>(identifier, typeStr));
                
            }

            // get declaration just 
            #region getDeclations
            List<VariableDeclarationSyntax> varNodes = body.DescendantNodes().OfType<VariableDeclarationSyntax>().ToList();

            foreach (VariableDeclarationSyntax varNode in varNodes)
            {
                foreach (VariableDeclaratorSyntax v in varNode.Variables)
                {
                    varTypePairs.Add(new Tuple<string, string>(v.Identifier.ToString(), varNode.Type.ToString()));
                }
            }
            #endregion

            //AssignmentExpressionSyntax

            // Check that every collected observer method is in a PexObserve.ValueForViewing calls
            List<InvocationExpressionSyntax> expressionNodes = body.DescendantNodes().OfType<InvocationExpressionSyntax>().ToList();
            foreach (InvocationExpressionSyntax expr in expressionNodes)
            {
                if (expr.ToString().Contains("PexObserve"))
                {
                    List<ArgumentSyntax> argList = expr.ArgumentList.Arguments.ToList();
                    string arg = argList[1].ToString();
                    string type = "";
                    
                    foreach (Tuple<string, string> varTypePair in varTypePairs)
                    {
                        if (varTypePair.Item1 == arg)
                        {
                            type = varTypePair.Item2;
                            break;
                        }
                    }

                    Debug.Assert(type != "");
                    observerMethods.Add(new Tuple<string, string>(arg, type));
                }
            }
            return observerMethods;
        }
         public SemanticModel getSemanticModel(SyntaxTree tree)
         {
            Debug.Assert(tree != null, "assume input tree is not null");
            //Compile -> Get Semantic model -> get type info later on
            var options = new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary);
            IReadOnlyList<MetadataReference> referencesForCompilation = this.targetProject.MetadataReferences;

            //Compile -> Get Semantic model -> get type info later on
            CSharpCompilation compilation = CSharpCompilation.Create("ArrayListTest")
                                           .AddReferences(referencesForCompilation)
                                           .AddSyntaxTrees(tree)
                                           .WithOptions(options);
            //var results = compilation.GetSymbolsWithName(sym =>true) ; 
            //var assem = compilation.Assembly;
            //var typeNames = assem.TypeNames;
            //assem.ToDisplayString();
            SemanticModel model = compilation.GetSemanticModel(tree);
            Debug.Assert(model != null);
            return model;
         }

        // Note: $var with "Name" doesn't need to be path, but $var without "Name" should be the exact path
        public List<Tuple<string, string>> ObserverMethodsExtraction(string testFileName, string PUTName)
        {
            List<Tuple<string, string>> observerMethods = new List<Tuple<string, string>>();
            List<Tuple<string, string>> varTypePairs = new List<Tuple<string, string>>();

            Document testClassDocument = FindDocumentByName(testFileName);

            /**** DEBUG ****/
            Debug.Assert(testClassDocument != null, "testClassDocument is null --- either it doesnt exists or cannot be found");

            DocumentEditor testClassEditor = DocumentEditor.CreateAsync(testClassDocument).Result;
            SyntaxTree testClassTree = testClassDocument.GetSyntaxTreeAsync().Result;
            SyntaxNode testClassRoot = testClassTree.GetRoot();

            // Find target method
            List<MethodDeclarationSyntax> testClassMethods = testClassRoot.DescendantNodes().OfType<MethodDeclarationSyntax>().ToList();
            int targetMethodIdx = FindMethodSyntaxIdxByName(testClassMethods, PUTName);
            MethodDeclarationSyntax targetMethod = testClassMethods[targetMethodIdx];

            //Get parameters of target method
            List<ParameterSyntax> parameters = targetMethod.ParameterList.Parameters.ToList();

            string pexVarName = "";
            foreach (ParameterSyntax p in parameters)
            {
                if (p.ToString().Contains("[PexAssumeUnderTest]"))
                {
                    pexVarName = p.Identifier.ToString();
                }

                varTypePairs.Add(new Tuple<string, string>(p.Identifier.ToString(), p.Type.ToString()));
            }
            // Debug.Assert(pexVarName != "");
            if (pexVarName == "")
            {
                Console.WriteLine("[INFO] There are no [PexAssumeUnderTest] in the arguments!");
            }

            // get body
            BlockSyntax body = targetMethod.Body;
            List<VariableDeclarationSyntax> varNodes = body.DescendantNodes().OfType<VariableDeclarationSyntax>().ToList();

            foreach (VariableDeclarationSyntax varNode in varNodes)
            {
                foreach (VariableDeclaratorSyntax v in varNode.Variables)
                {
                    varTypePairs.Add(new Tuple<string, string>(v.Identifier.ToString(), varNode.Type.ToString()));
                }
            }
            
            //AssignmentExpressionSyntax

            // Check that every collected observer method is in a PexObserve.ValueForViewing calls
            List<InvocationExpressionSyntax> expressionNodes = body.DescendantNodes().OfType<InvocationExpressionSyntax>().ToList();
            foreach (InvocationExpressionSyntax expr in expressionNodes)
            {
                if (expr.ToString().Contains("PexObserve"))
                {
                    List<ArgumentSyntax> argList = expr.ArgumentList.Arguments.ToList();
                    string arg = argList[1].ToString();
                    string type = "";

                    foreach (Tuple<string, string> varTypePair in varTypePairs)
                    {
                        if (varTypePair.Item1 == arg)
                        {
                            type = varTypePair.Item2;
                            break;
                        }
                    }

                    Debug.Assert(type != "");
                    observerMethods.Add(new Tuple<string, string>(arg, type));
                }
            }
            return observerMethods;
        }

        private static int FindMethodSyntaxIdxByName(List<MethodDeclarationSyntax> methods, string methodName)
        {
            for (int i = 0; i < methods.Count; i++)
            {
                if (methods[i].Identifier.ToString().Equals(methodName))
                {
                    return i;
                }
            }
            return -1;
        }
        private Project findProjectByName(string projectName)
        {
            foreach (Project proj in this.solution.Projects)
            {
                if (proj.Name.Equals(projectName))
                {
                    return proj;
                }
            }
            return null;
        }
        private Document FindDocumentByName(string fileName)
        {
            
            foreach (Document document in this.targetProject.Documents)
            {
                if (document.Name.Equals(fileName))
                {
                    return document;
                }
            }
            
            return null;
        }

        public void WriteObserversToFile(string outputFile, List<Tuple<string, string>> observerMethods)
        {
            using (StreamWriter file = new StreamWriter(outputFile))
            {
                foreach (Tuple<string, string> varTypePair in observerMethods)
                {
                    file.WriteLine(varTypePair.Item1 + " " + varTypePair.Item2);
                }
            }
        }
    }
}
