import command_runner

from Data.problem import Problem

class Instrumenter:

    #  Name of compiler executable
    buildExe = ""
    # Name of roslyn executable
    inserterExe = ""

    def __init__(self, buildExec, inserterExec):
        self.buildExe = buildExec
        self.inserterExe = inserterExec

    def instrumentPost(self, problem, post,PUTName):
        
        instCommand =self.getInstrumentationCommand(problem, post, PUTName)
        instOutput = command_runner.runCommand(instCommand)
        
        
        buildCommand = self.getMsbuildCommand(problem)
        buildOutput = command_runner.runCommand(buildCommand)
        
        #print(buildOutput)

    def getInstrumentationCommand(self, problem, postcondition,PUTName):
        instruCommand = self.inserterExe + " --solution=" + problem.sln + \
        " --test-project-name=" +problem.projectName+ " --test-file-name=" +problem.testFileName+ " --PUT-name=" +PUTName+ " --post-condition="+"\""+postcondition.toInfix()+"\""
        return instruCommand

    def getMsbuildCommand(self,problem):
        buildCommand = self.buildExe+" " +problem.sln+ " /t:rebuild"
        return buildCommand

    def instrumentPostString(self, problem, post,PUTName):
        
        instCommand =self.getInstrumentationCommandString(problem, post, PUTName)
        instOutput = command_runner.runCommand(instCommand)
        
        
        buildCommand = self.getMsbuildCommand(problem)
        buildOutput = command_runner.runCommand(buildCommand)

    def getInstrumentationCommandString(self, problem, postcondition,PUTName):
        instruCommand = self.inserterExe + " --solution=" + problem.sln + \
        " --test-project-name=" +problem.projectName+ " --test-file-name=" +problem.testFileName+ " --PUT-name=" +PUTName+ " --post-condition="+"\""+postcondition+"\""
        return instruCommand