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

        public Utility(string sln)
        {
            Debug.Assert(File.Exists(sln));
            this.workspace = MSBuildWorkspace.Create();
            this.solution = workspace.OpenSolutionAsync(sln).Result;
        }

        // Note: $var with "Name" doesn't need to be path, but $var without "Name" should be the exact path
        public List<Tuple<string, string>> ObserverMethodsExtraction(string testProjectName, string testFileName, string PUTName)
        {
            List<Tuple<string, string>> observerMethods = new List<Tuple<string, string>>();
            List<Tuple<string, string>> varTypePairs = new List<Tuple<string, string>>();

            Document testClassDocument = FindDocumentByName(testProjectName, testFileName);

            /**** DEBUG ****/
            Debug.Assert(testClassDocument != null);

            DocumentEditor testClassEditor = DocumentEditor.CreateAsync(testClassDocument).Result;
            SyntaxTree testClassTree = testClassDocument.GetSyntaxTreeAsync().Result;
            SyntaxNode testClassRoot = testClassTree.GetRoot();

            List<MethodDeclarationSyntax> testClassMethods = testClassRoot.DescendantNodes().OfType<MethodDeclarationSyntax>().ToList();
            int targetMethodIdx = FindMethodSyntaxIdxByName(testClassMethods, PUTName);
            MethodDeclarationSyntax targetMethod = testClassMethods[targetMethodIdx];

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
            //Debug.Assert(pexVarName != "");

            BlockSyntax body = targetMethod.Body;
            List<VariableDeclarationSyntax> varNodes = body.DescendantNodes().OfType<VariableDeclarationSyntax>().ToList();
            foreach (VariableDeclarationSyntax varNode in varNodes)
            {
                foreach (VariableDeclaratorSyntax v in varNode.Variables)
                {
                    varTypePairs.Add(new Tuple<string, string>(v.Identifier.ToString(), varNode.Type.ToString()));
                }
            }

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

        private Document FindDocumentByName(string projectName, string fileName)
        {
            foreach (Project project in this.solution.Projects)
            {
                if (project.Name.Equals(projectName))
                {
                    foreach (Document document in project.Documents)
                    {
                        if (document.Name.Equals(fileName))
                        {
                            return document;
                        }
                    }
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
