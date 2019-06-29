using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.IO;
using System.Text;
using System.Threading.Tasks;

namespace ObserverTypeExtractor
{
    class Program
    {
        static void Main(string[] args)
        {
            if (args.Count() != 5)
            {
                ShowHelpMessage();
                return;
            }

            Debug.Assert(Path.GetExtension(args[0]).Equals(".sln"), "input args[0] should be a solution file!");
            string sln = Path.GetFullPath(args[0]);
            string projectName = args[1];
            string testFileName = args[2];
            string PUTName = args[3];
            string outputFile = Path.GetFullPath(args[4]);

            Utility utility = new Utility(sln);
            // List<Tuple<string, string>> observerMethods = utility.ObserverMethodsExtraction("StackTest", "StackContractTest.cs", "PUT_PushContract");
            List<Tuple<string, string>> observerMethods = utility.ObserverMethodsExtraction(projectName, testFileName, PUTName);
            utility.WriteObserversToFile(outputFile, observerMethods);
        }

        public static void ShowHelpMessage()
        {
            Console.WriteLine("Arguments: <solutionPath> <projectName> <testFileName> <PUTName> <outputFile>");
        }
    }
}
