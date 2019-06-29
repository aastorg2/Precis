import itertools
import os
from precis_var import PrecisVar
from z3 import *

class Problem:
    def __init__(self, sln, projectName, testFileName, PUTs):
        self.sln = sln
        self.projectName = projectName
        self.testFileName = testFileName
        self.PUTs = PUTs

    # Use C# code to extract the observer methods and corresponding types to an output file
    def ExtractObservers(self, PUTName, outputFile):
        assert PUTName in self.PUTs, 'PUTName not found or does not match PUTs given in constructor!!!'
        observerExtractor = os.path.abspath('./ObserverExtractor/ObserverExtractor/bin/Debug/ObserverExtractor.exe')
        cmd = observerExtractor + ' ' + self.sln + ' ' + self.projectName + ' ' + self.testFileName + ' ' + PUTName + ' ' + outputFile
        os.system(cmd)

    # Read the output file and parse the observer methods
    def ReadObserversFromFile(self, outputFile):
        pvarList = []
        with open(outputFile) as f:
            lines = f.readlines()
        for line in lines:
            line = line.strip().split()
            varName = line[0]
            varType = line[1]
            pvarList.append(PrecisVar(varName, varType, varName.startswith("New_")))
        return pvarList

if __name__ == '__main__':
    sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
    projectName =  'StackTest' 
    testFileName = 'StackContractTest.cs' 
    PUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract'] 
    PUTName = 'PUT_PushContract'
    outputFile = os.path.abspath('./typesOM.txt')

    p = Problem(sln, projectName, testFileName, PUTs)
    print(PUTName in p.PUTs)
    p.ExtractObservers(PUTName, outputFile)
    pvarList = p.ReadObserversFromFile(outputFile)
    print(pvarList[1].varName)
    print(pvarList[1].varZ3)
    print(pvarList[1].isNew)