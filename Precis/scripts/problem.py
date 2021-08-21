import itertools
import os
from precis_feature import PrecisFeature
from z3 import *

# TODO:
# Parsing the .cs file to get list of the PUTs
# Keep them as a field of class for validation
# Can be implemented as client C# code!!!

class Problem:
    def __init__(self, sln, projectName, testDebugFolder, testDll, testFileName, testNamespace, testClass, daikonTestFilePath,puts):
        self.sln = sln
        self.projectName = projectName
        self.testDebugFolder = testDebugFolder
        self.testDll = testDll
        self.testFileName = testFileName
        self.testNamespace = testNamespace
        self.testClass = testClass
        self.daikonTestFilePath =daikonTestFilePath
        self.puts = puts

    def writeTests(self,tests):
        daikonTestFullPath = os.path.abspath(self.daikonTestFilePath)
        with open(daikonTestFullPath, 'r') as f:
            lines = f.readlines()
        
        original = []
        firstBracket = False
        for idx in range(0,len(lines)):
            
            if "public partial" in lines[idx] and "{" not in lines[idx]:
                firstBracket = True                 

            if "{" in lines[idx] and firstBracket:
                firstBracket = False
                original =lines[0:idx+1]
                original = original + tests
            
            if "public partial" in lines[idx] and "{" in lines[idx]:
                original =lines[0:idx+1]
                original = original + tests
        
        with open(daikonTestFullPath, 'w') as fwrite:
            for line in original:
                fwrite.write(str(line))
            fwrite.write("    }\n}\n")

    # Use C# code to extract the observer methods and corresponding types to an output file
    def ExtractObservers(self, PUTName, outputFile, mode, oe_path):
        # assert PUTName in self.PUTs, 'PUTName not found or does not match PUTs given in constructor!!!'
        observerExtractor = os.path.abspath('../Precis/ObserverExtractor/ObserverExtractor/bin/Debug/ObserverExtractor.exe')
        cmd = observerExtractor + ' ' + self.sln + ' ' + self.projectName + ' ' + self.testFileName + ' ' + PUTName + ' ' + outputFile + ' ' +mode
        os.system(cmd)
    
    # Use C# code to extract the observer methods and corresponding types to an output file
    def ExtractObserversInPUT(self, PUTName, outputFile, mode, oe_path, temp_path):
        # assert PUTName in self.PUTs, 'PUTName not found or does not match PUTs given in constructor!!!'
        observerExtractor = os.path.abspath(oe_path) # os.path.abspath('../Precis/ObserverExtractor/ObserverExtractor/bin/Debug/ObserverExtractor.exe')
        cmd = observerExtractor + ' ' + self.sln + ' ' + self.projectName + ' ' + self.testFileName + ' ' + PUTName + ' ' + outputFile + ' ' + mode
        ret = os.system(cmd)
        tmp = open(f'{temp_path}\\command_observer_Class.txt', 'w') # open("./temp/command_observer_PUT.txt", 'w')
        tmp.write(cmd)
        tmp.close()
        if ret == -532462766 or ret == 1:
            print("Error: Exception in oberserver extractor")
            sys.exit()

    def ExtractObserversInClass(self, outputFile, mode, oe_path, temp_path):
        # assert PUTName in self.PUTs, 'PUTName not found or does not match PUTs given in constructor!!!'
        observerExtractor = os.path.abspath(oe_path) # os.path.abspath('../Precis/ObserverExtractor/ObserverExtractor/bin/Debug/ObserverExtractor.exe')
        PUTName = "Dummy"
        cmd = observerExtractor + ' ' + self.sln + ' ' + self.projectName + ' ' + self.testFileName + ' ' + PUTName + ' ' + outputFile + ' ' + mode
        ret = os.system(cmd)
        tmp = open(f'{temp_path}\\command_observer_Class.txt', 'w') # open(".\\temp\\command_observer_Class.txt", 'w')
        tmp.write(cmd)
        tmp.close()

    # Read the output file and parse the observer methods
    def ReadObserversFromFile(self, outputFile):
        precisFeatureTuple = ()
        with open(outputFile) as f:
            lines = f.readlines()
        for line in lines:
            #consider checking that all variables start with "Old" or "New"
            line = line.strip().split()
            varName = line[0]
            varType = line[1]
            if varType.upper() == 'INT' or varType.upper() == 'BOOL' or varType.upper() == 'FLOAT': 
                precisFeatureTuple += (PrecisFeature(False, varName, varType, varName.startswith("New_"), None),)
            
        return precisFeatureTuple

    
# if __name__ == '__main__':
#     sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
#     projectName =  'StackTest' 
#     testDebugFolder = '../ContractsSubjects/Stack/StackTest/bin/Debug/'
#     testDll = testDebugFolder + 'StackTest.dll'
#     testFileName = 'StackContractTest.cs' 
#     testNamepace = 'Stack.Test'
#     testClass = 'StackContractTest'
#     PUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract'] 
#     PUTName = 'PUT_PushContract'
#     outputFile = os.path.abspath('./typesOM.txt')

#     p = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass, PUTs)
#     print(PUTName in p.PUTs)
#     p.ExtractObservers(PUTName, outputFile)
#     p.ReadObserversFromFile(outputFile)
#     print(p.precisFeatureList[1].varName)
#     print(p.precisFeatureList[1].varZ3)
#     print(p.precisFeatureList[1].isNew)