import os
from os import sys, path
from z3 import *
from Data.problem import Problem
from Teachers.pex import Pex
from Learners.feature_synthesis import FeatureSynthesis
from Learners.houdini import Houdini

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

    #returns list of base features
    baseFeatures = p.ReadObserversFromFile(outputFile)
    
    pex = Pex()
    baseFeatureVectors = pex.RunTeacher(p, PUTName, baseFeatures)
    
    featureSynthesizer = FeatureSynthesis()
    #list of derivedFeatures
    derivedFeatures = featureSynthesizer.GenerateDerivedFeatures(baseFeatures)
    
    features = list()
    # appending two list
    features =  baseFeatures + derivedFeatures

    houdini = Houdini()
    derivedFeatureVectors = list()

    # derivedFeatureVectors is a list of tuples of Z3 values
    derivedFeatureVectors = houdini.generateDerivedFeatureVectors(derivedFeatures, baseFeatures, baseFeatureVectors)

    # keep feature vectors as list, once appended turn to set
    print ("base Feature Vectors: ", baseFeatureVectors)
    print("\n")
    print("derived feature vectors: ", derivedFeatureVectors)
    print("\n")
    print ("all features: ", features)

    # derivedFeatureVectors is a list of tuples of Z3 values
    featureVectors = houdini.concatenateFeatureVectors(baseFeatureVectors, derivedFeatureVectors)
    print(featureVectors)
    print('Here')

    #assert(bfv[0] <--> dfv[0] )
    #featureVectors = baseFeatureVectors + derivedFeatureVectors
    #print(derivedFeatures)
    #print(featureVectors)










if __name__ == '__main__':
    learnPost()