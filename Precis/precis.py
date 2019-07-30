import os
from os import sys, path
from z3 import *
from Data.problem import Problem
from Teachers.pex import Pex
from Learners.feature_synthesis import FeatureSynthesis
from Learners.houdini import Houdini
from Learners.disjunctive_learner import DisjunctiveLearner
from Teachers.instrumenter import Instrumenter
import command_runner

import logging


def learnPost(p,PUTName, outputFile):

    logger = logging.getLogger("Runner")
    logger.setLevel(logging.INFO)
    # create the logging file handler
    fh = logging.FileHandler("information")
    formatter = logging.Formatter('%(message)s')
    fh.setFormatter(formatter)
    # add handler to logger object
    logger.addHandler(fh)


    
    p.ExtractObservers(PUTName, outputFile)

    #returns list of base features
    baseFeatures = p.ReadObserversFromFile(outputFile)
    allPostconditions = list()
    allBaseFeatureVectors =[]
    while True:
        pex = Pex()
        
        baseFeatureVectors = pex.RunTeacher(p, PUTName, baseFeatures)
        allBaseFeatureVectors.extend(baseFeatureVectors)
        featureSynthesizer = FeatureSynthesis()
        #list of derivedFeatures
        derivedFeatures = featureSynthesizer.GenerateDerivedFeatures(baseFeatures)
        features = list()
        # appending two list
        features =  baseFeatures + derivedFeatures

        houdini = Houdini()
        derivedFeatureVectors = list()
        # derivedFeatureVectors is a list of tuples of Z3 values
        derivedFeatureVectors = houdini.generateDerivedFeatureVectors(derivedFeatures, baseFeatures, allBaseFeatureVectors)
        # derivedFeatureVectors is a list of tuples of Z3 values
        featureVectors = houdini.concatenateFeatureVectors(allBaseFeatureVectors, derivedFeatureVectors)
        #print(featureVectors)
        
        boolFeatures, boolFeatureIndices = houdini.getBoolFeatures(features)
        boolFeatureVectors = houdini.getBoolFeatureVectors(featureVectors, boolFeatureIndices)
        
        postcondition = None
        disLearner = DisjunctiveLearner()
        postcondition = disLearner.learn(0,boolFeatures, boolFeatureVectors)
        #sys.exit(0)
        print("before to infix")
        print(postcondition.toInfix())
        
        # assumes ms build in path
        inst = Instrumenter("MSBuild.exe","./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
        inst.instrumentPost(p, postcondition, PUTName)    

        if postcondition.formula in allPostconditions:
            print("found it")
            break
        
        allPostconditions.append(postcondition.formula)
        #assert(bfv[0] <--> dfv[0] )
        #featureVectors = baseFeatureVectors + derivedFeatureVectors
        #print(derivedFeatures)
        #print(featureVectors)

if __name__ == '__main__':
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
    
    learnPost(p, PUTName, outputFile)