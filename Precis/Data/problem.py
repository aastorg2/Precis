import itertools
import os
from precis_var import PrecisVar
from z3 import *

class Problem:
    def __init__(self):
        pass

    # Use C# code to extract the observer methods and corresponding types to an output file
    def ExtractObservers(self, sln, projectName, testFileName, PUTName, outputFile):
        observerExtractor = os.path.abspath('./ObserverExtractor/ObserverExtractor.exe')
        cmd = observerExtractor + ' ' + sln + ' ' + projectName + ' ' + testFileName + ' ' + PUTName + ' ' + outputFile
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
    sln = os.path.abspath('./ContractSubjects/Stack/Stack.sln')
    projectName =  'StackTest' 
    testFileName = 'StackContractTest.cs' 
    PUTName = 'PUT_PushContract' 
    outputFile = os.path.abspath('./typesOM.txt')

    p = Problem()
    p.ExtractObservers(sln, projectName, testFileName, PUTName, outputFile)
    pvarList = p.ReadObserversFromFile(outputFile)
    print(pvarList[1].varName)
    print(pvarList[1].varZ3)
    print(pvarList[1].isNew)