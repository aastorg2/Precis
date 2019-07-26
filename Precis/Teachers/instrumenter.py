import command_runner

from Data.problem import Problem

class Instrumenter:

    buildExe = ""
    inserterExe = ""

    def __init__(self, buildExec, inserterExec):
        self.buildExe = buildExec
        self.inserterExe = inserterExec

    def instrumentPost(self, problem, post):

        buildCommand = self.getMsbuildCommand(problem)
        buildOutput = command_runner.runCommand(buildCommand)
        
        print(buildOutput)

    def getMsbuildCommand(self,problem):
        buildCommand = "MSBuild.exe " +problem.sln+ " /t:rebuild"
        return buildCommand

