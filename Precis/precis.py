import os
from os import sys, path
from z3 import *
from Data.problem import Problem
from Teachers.pex import Pex
from Learners.feature_synthesis import FeatureSynthesis
from Learners.houdini import Houdini
from Learners.disjunctive_learner import DisjunctiveLearner
from Teachers.instrumenter import Instrumenter
from Data.precis_formula import PrecisFormula
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
    #todo: test for k==2
    #post = learnPostUpToK(p,PUTName,outputFile,0)
    postK1 = learnPostUpToK(p,PUTName, outputFile,1)
    #postK2 = learnPostUpToK(p,PUTName, outputFile,2)
    #print("smallest post up to k == 0", post.toInfix())
    print("smallest post up k == 1",postK1.toInfix())
    #print("smallest post up k == 2",postK2.toInfix())
    """
    implication = Implies(post.formulaZ3,postK1.formulaZ3)
    solver0 = Solver()
    solver0.add(Not(implication)) # check (not (post => post1)) is unsat
    check0 = solver0.check()
    logger.info("first check\n")
    logger.info(solver0.to_smt2())
    print("is it unsat?", check0 ) # if unsat, stop
    otherside = Implies(postK1.formulaZ3,postK2.formulaZ3)
    solver1 = Solver()
    solver1.add(Not(otherside))
    check1 = solver1.check()
    print("is it unsat?", check1 )
    """
def learnPostUpToK(p,PUTName, outputFile, k):

    p.ExtractObservers(PUTName, outputFile)

    #returns list of base features
    baseFeatures = p.ReadObserversFromFile(outputFile)
    allPostconditions = list()
    allBaseFeatureVectors =[]
    
    inst = Instrumenter("MSBuild.exe","./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    initFormula = PrecisFormula(BoolVal(False))
    inst.instrumentPost(p,initFormula , PUTName)

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
        postcondition = disLearner.learn(k,boolFeatures, boolFeatureVectors)
        #sys.exit(0)
        print("postcondition formulaZ3")
        print(postcondition.formulaZ3)
        print("postcondition formula")
        print(postcondition.formula)
        print("postcondition infix")
        print(postcondition.toInfix())
        
        # assumes ms build in path
        inst = Instrumenter("MSBuild.exe","./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
        inst.instrumentPost(p, postcondition, PUTName)    

        if postcondition.formula in allPostconditions:
            print("found it")
            return postcondition
        
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