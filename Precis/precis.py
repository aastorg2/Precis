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
    # derivedFeatureVectors is a list of tuples of Z3 values
    featureVectors = houdini.concatenateFeatureVectors(baseFeatureVectors, derivedFeatureVectors)
    #print(featureVectors)
    
    boolFeatures, boolFeatureIndices = houdini.getBoolFeatures(features)
    boolFeatureVectors = houdini.getBoolFeatureVectors(featureVectors, boolFeatureIndices)
    #print()
    #print(boolFeatures)
    #print()
    #print(boolFeatureIndices)
    #print()
    #print(boolFeatureVectors)
    postcondition = None
    postcondition = houdini.learn(boolFeatures, boolFeatureVectors)
    
    #assert(bfv[0] <--> dfv[0] )
    #featureVectors = baseFeatureVectors + derivedFeatureVectors
    #print(derivedFeatures)
    #print(featureVectors)










if __name__ == '__main__':
    learnPost()