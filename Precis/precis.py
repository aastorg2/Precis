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
    
    (postK2,r2) = learnPostUpToK(p,PUTName, outputFile,2)
    #print("smallest post up to k == 2", postK2.toInfix())
    #sys.exit(0)
    (postK1,r1) = learnPostUpToK(p,PUTName, outputFile,1)
    #print("smallest post up to k == 2", postK1.toInfix())
    #sys.exit(0)
    (postK0,r0) = learnPostUpToK(p,PUTName,outputFile,0)
    #print("smallest post up to k == 0", postK0.toInfix())
    #sys.exit(0)
    
    return (postK0, r0, postK1, r1 , postK2, r2)
    
    

def learnPostUpToK(p,PUTName, outputFile, k):

    p.ExtractObservers(PUTName, outputFile)

    #returns list of base features
    baseFeatures = p.ReadObserversFromFile(outputFile)
    allPostconditions = list()
    allBaseFeatureVectors =[]
    
    inst = Instrumenter("MSBuild.exe","./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    initFormula = PrecisFormula(BoolVal(False))
    inst.instrumentPost(p,initFormula , PUTName)
    rounds = 0
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
        indices = list()
        (postcondition, indices) = disLearner.learn2(k,boolFeatures, boolFeatureVectors,"root")
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
            return postcondition, rounds
        
        allPostconditions.append(postcondition.formula)
        rounds = rounds + 1
        #assert(bfv[0] <--> dfv[0] )
        #featureVectors = baseFeatureVectors + derivedFeatureVectors
        #print(derivedFeatures)
        #print(featureVectors)

#todo: list of problems
def runLearnPost(p, putList,outputFile):
    #assert puts in putList in problem
    for PUTName in putList:
        # post = learnPost(p,PUTName, outputFile)
        logger1.info("PUT: "+PUTName+"\n")
        (postK0,r0, postK1,r1,postK2,r2) = learnPost(p, PUTName, outputFile)
        logger1.info("postcondition k == 0\n "+ postK0.toInfix()+"\nrounds: "+str(r0)+"\n")
        logger1.info("postcondition k == 1\n "+ postK1.toInfix()+"\nrounds: "+str(r1)+"\n")
        logger1.info("postcondition k == 2\n "+ postK2.toInfix()+"\nrounds: "+str(r2)+"\n")
        print("postcondition k == 0 ", postK0.toInfix(), "rounds: ", r0)
        print("postcondition k == 1 ", postK1.toInfix(), "rounds: ", r1)
        print("postcondition k == 2 ", postK2.toInfix(), "rounds: ", r2)
        
        implication = Implies(postK0.formulaZ3,postK1.formulaZ3)
        solver0 = Solver()
        solver0.add(Not(implication)) # check (not (postK0 => postK1)) is unsat
        check0 = solver0.check()
        #logger.info("first check\n")
        #logger.info(solver0.to_smt2())
        logger1.info("is it unsat Not(k0 -> k1)? "+ str(check0)+"\n")
        print("is it unsat?", check0 ) # if unsat, stop
        nextImplication = Implies(postK1.formulaZ3,postK2.formulaZ3) # check (not (postK1 => postK2)) is unsat
        solver1 = Solver()
        solver1.add(Not(nextImplication))
        check1 = solver1.check()
        logger1.info("is it unsat? Not(k1 -> k2)"+ str(check1)+"\n")
        print("is it unsat?", check1)
        nextNextImplication = Implies(postK0.formulaZ3,postK2.formulaZ3) # check (not (postK1 => postK2)) is unsat
        solver2 = Solver()
        solver2.add(Not(nextNextImplication))
        check2 = solver2.check()
        logger1.info("is it unsat? Not(k0 -> k2)"+ str(check1)+"\n")
        print("is it unsat?", check2)

if __name__ == '__main__':

    logger = logging.getLogger("Runner")
    logger.setLevel(logging.INFO)
    # create the logging file handler
    fh = logging.FileHandler("information")
    formatter = logging.Formatter('%(message)s')
    fh.setFormatter(formatter)
    # add handler to logger object
    logger.addHandler(fh)

    logger1 = logging.getLogger("Results")
    logger1.setLevel(logging.INFO)
    fh1 = logging.FileHandler("results")
    formatter1 = logging.Formatter('%(message)s')
    fh1.setFormatter(formatter1)
    logger1.addHandler(fh1)


    sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
    projectName =  'StackTest'
    testDebugFolder = '../ContractsSubjects/Stack/StackTest/bin/Debug/'
    testDll = testDebugFolder + 'StackTest.dll'
    testFileName = 'StackContractTest.cs' 
    testNamepace = 'Stack.Test'
    testClass = 'StackContractTest'
    stackPUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract'] 
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    outputFile = os.path.abspath('./typesOM.txt')

    p = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    #runLearnPost(p,stackPUTs,outputFile)

    sln = os.path.abspath('../ContractsSubjects/HashSet/HashSet.sln')
    projectName =  'HashSetTest'
    testDebugFolder = '../ContractsSubjects/HashSet/HashSetTest/bin/Debug/'
    testDll = testDebugFolder + 'HashSetTest.dll'
    testFileName = 'HashSetContractTest.cs' 
    testNamepace = 'HashSet.Test'
    testClass = 'HashSetContractTest'
    hashsetPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_CountContract', 'PUT_ContainsContract'] 
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    outputFile = os.path.abspath('./typesOM.txt')

    p1 = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)

    runLearnPost(p1,hashsetPUTs,outputFile)

        