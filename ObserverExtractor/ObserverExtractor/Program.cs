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
            if (args.Count() < 6)
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
            string mode = args[5];

            Utility utility = new Utility(sln, projectName);
            // List<Tuple<string, string>> observerMethods = utility.ObserverMethodsExtraction("StackTest", "StackContractTest.cs", "PUT_PushContract");
            // List<Tuple<string, string>> observerMethods = utility.ObserverMethodsExtraction(testFileName, PUTName);
            List<Tuple<string, string>> observerMethods = new List<Tuple<string, string>>();
            if (mode.Equals("daikonMethod"))
            {
                observerMethods = utility.ObserverMethodsExtractionForDaikon(testFileName, PUTName);
            }
            else if (mode.Equals("daikonClass"))
            {
                observerMethods = utility.ObserverMethodsExtractionInClassForDaikon(testFileName, PUTName);
            }
            else
            {

                observerMethods = utility.ObserverMethodsExtraction(testFileName, PUTName);
            }
            utility.WriteObserversToFile(outputFile, observerMethods);
        }

        public static void ShowHelpMessage()
        {
            Console.WriteLine("Arguments: <solutionPath> <projectName> <testFileName> <PUTName> <outputFile>");
        }
    }
}
