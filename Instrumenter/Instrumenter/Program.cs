using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.IO;
using System.Text;
using System.Threading.Tasks;
using Mono.Options;

namespace ObserverTypeExtractor
{
    class Program
    {
        static void Main(string[] args)
        {
            bool showHelp = false;
            string sln = "";
            string testProjectName = "";
            string testFileName = "";
            string PUTName = "";
            string postCondition = "";

            var optionSet = new OptionSet() {
                { "solution=", "Path of solution", v => sln = v },
                { "test-project-name=", "Project name", v => testProjectName = v },
                { "test-file-name=", "Test file name", v => testFileName = v },
                { "PUT-name=", "PUT Name", v => PUTName = v },
                { "post-condition=", "Post condition", v => postCondition = v },
            };

            try {
                optionSet.Parse(args);
                //Console.WriteLine(sln);
                //Console.WriteLine(testProjectName);
                //Console.WriteLine(testFileName);
                //Console.WriteLine(PUTName);
                //Console.WriteLine(postCondition);
            }
            catch (OptionException e) {
                Console.Write("Instrumenter.exe ");
                Console.WriteLine(e.Message);
                Console.WriteLine("Try `Instrumenter.exe --help' for more information.");
                return;
            }

            if (showHelp)
            {
                ShowHelpMessage();
                return;
            }

            Debug.Assert(Path.GetExtension(sln).Equals(".sln"), "input args[0] should be a solution file!");
            Utility utility = new Utility(sln, testProjectName, testFileName);
            utility.PostConditionInsertion(PUTName, postCondition);
        }

        public static void ShowHelpMessage()
        {
            Console.WriteLine("Instrumenter.exe --solution=<> --project-name=<> --test-file-name=<>" +
                " --PUT-name=<> --post-condition=<>");
        }
    }
}
