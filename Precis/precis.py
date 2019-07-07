import os
from os import sys, path
from z3 import *
from Data.problem import Problem
from Teachers.pex import Pex
from Learners.feature_synthesis import FeatureSynthesis


def learnPost():
    sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
    projectName =  'StackTest' 
    testDebugFolder = '../ContractsSubjects/Stack/StackTest/bin/Debug/'
    testDll = testDebugFolder + 'StackTest.dll'
    testFileName = 'StackContractTest.cs' 
    testNamepace = 'Stack.Test'
    testClass = 'StackContractTest'
    PUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract'] 
    PUTName = 'PUT_PushContract'
    outputFile = os.path.abspath('./typesOM.txt')

    p = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    p.ExtractObservers(PUTName, outputFile)

    # returns list of base features
    pvarList = p.ReadObserversFromFile(outputFile)

    pex = Pex()
    featureVectors = pex.RunTeacher(p, PUTName, pvarList)
    
    

    featureSynthesizer = FeatureSynthesis()
    #list of derivedFeatures
    derivedFeatures = featureSynthesizer.GenerateDerivedFeatures(pvarList)
    print(derivedFeatures)
    
    print(featureVectors)
    

    print ("here")










if __name__ == '__main__':
    learnPost()