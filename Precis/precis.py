import os
from os import sys, path
import time
from z3 import *
from Data.problem import Problem
from Data.precis_feature import PrecisFeature
from Data.precis_formula import PrecisFormula
from Data.feature_vector import FeatureVector
from Teachers.pex import Pex
from Learners.feature_synthesis import FeatureSynthesis
from Learners.houdini import Houdini
from Learners.disjunctive_learner import DisjunctiveLearner
from Teachers.instrumenter import Instrumenter
from featurizer import Featurizer
import command_runner
from typing import List, Tuple, Type


import logging


def learnPostUpToK(p, PUTName, outputFile, k):
    sygusExecutable = "Precis/Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "tempLocation"
    sygusFileName = "postcondition.sl"

    # assumes MSBuils.exe in path
    inst = Instrumenter(
        "MSBuild.exe", "./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")

    p.ExtractObservers(PUTName, outputFile)

    # returns list of base features
    baseFeatures: Tuple[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allPostconditions = []
    allBaseFeatureVectors = []

    # FixMe: feature synthesis object shoul be initialized with base features and the feature vector should be updated
    #synthesizer = FeatureSynthesis(sygusExecutable,tempLocation,sygusFileName, baseFeatures)
    synthesizer = FeatureSynthesis(
        sygusExecutable, tempLocation, sygusFileName)

    initFormula = PrecisFormula(BoolVal(False))
    inst.instrumentPost(p, initFormula, PUTName)
    rounds = 1
    while True:
        print("starting round: " + str(rounds))
        pex = Pex()

        startTimePex = time.time()
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(
            p, PUTName, baseFeatures)
        pexTime = time.time() - startTimePex
        print("pex time: " + str(pexTime))
        allBaseFeatureVectors.extend(baseFeatureVectors)

        intBaseFeatures, boolBaseFeatures = Featurizer.getIntAndBoolFeatures(
            baseFeatures)

        indices = []
        disLearner = DisjunctiveLearner(synthesizer)
        logger1.info("#############\nRound: "+str(rounds)+"\n")
        (postcondition, indices) = disLearner.learn3(
            k, intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors, (), "root")
        print("unsimplified post "+ postcondition.toInfix())
        # assumes ms build in path
        inst = Instrumenter(
            "MSBuild.exe", "./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
        inst.instrumentPost(p, postcondition, PUTName)

        if all(baseFeatureVectors[i].testLabel for i in range(0, len(baseFeatureVectors))):
            print("found it")
            simplifiedPost = PrecisFormula(postcondition.precisSimplify())
            return postcondition, simplifiedPost, rounds

        if rounds == 16:
            print("BAD!")
            simplifiedPost = PrecisFormula(postcondition.precisSimplify())
            return postcondition, simplifiedPost, rounds

        allPostconditions.append(postcondition.formula)
        rounds = rounds + 1

def runLearnPost(p, putList, projectName, outputFile, k = 1):
    #assert puts in putList in problem
    logger1.info("Problem: "+projectName+"\n")
    
    for PUTName in putList:
        # post = learnPost(p,PUTName, outputFile)
        logger1.info("PUT: "+PUTName+"\n")
        results = []
        for i in range(0, k+1):
            logger1.info("=====\nCase: k == "+str(i)+"\n")
            (post, simplePost, rounds) = learnPostUpToK(p, PUTName, outputFile,i)
            logger1.info("===== Final Result\n")
            logger1.info("postcondition k == "+str(i)+"\n" +
                        post.toInfix()+"\nrounds: " + str(rounds) + "\n")
            logger1.info("simple   post k == " + str(i) + "\n" +
                        simplePost.toInfix()+"\nrounds: "+str(rounds)+"\n")
            
            results.append((post, simplePost, rounds))
            if i > 0:
                implication = Implies(results[i-1][0].formulaZ3, results[i][0].formulaZ3)
                implication1 = Implies(results[i][0].formulaZ3, results[i-1][0].formulaZ3)
                solver1 = Solver()
                solver1.add(Not(implication1))
                check1 = solver1.check()
                logger1.info("Not(k"+str(i)+" -> k" + str(i-1) +"? " + str(check1)+"\n")
                
                solver = Solver()
                # check (not (postK0 => postK1)) is unsat
                solver.add(Not(implication))
                check = solver.check()
                logger1.info("Not(k"+str(i-1)+" -> k" + str(i) +"? " + str(check)+"\n")
        
        sys.exit(0)

            


if __name__ == '__main__':
    # region logger
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
    # endregion
    outputFileType = os.path.abspath('./typesOM.txt')
    subjects = []
    
    # Stack
    sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
    projectName = 'StackTest'
    testDebugFolder = '../ContractsSubjects/Stack/StackTest/bin/Debug/'
    testDll = testDebugFolder + 'StackTest.dll'
    testFileName = 'StackContractTest.cs'
    testNamepace = 'Stack.Test'
    testClass = 'StackContractTest'
    stackPUTs = ['PUT_PushContract', 'PUT_PopContract',
                 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']
    

    p = Problem(sln, projectName, testDebugFolder, testDll,
                testFileName, testNamepace, testClass,stackPUTs )
    
    subjects.append(p)
    #End of Stack

    # HashSet
    sln = os.path.abspath('../ContractsSubjects/HashSet/HashSet.sln')
    projectName = 'HashSetTest'
    testDebugFolder = '../ContractsSubjects/HashSet/HashSetTest/bin/Debug/'
    testDll = testDebugFolder + 'HashSetTest.dll'
    testFileName = 'HashSetContractTest.cs'
    testNamepace = 'HashSet.Test'
    testClass = 'HashSetContractTest'
    hashsetPUTs = ['PUT_AddContract', 'PUT_RemoveContract',
                   'PUT_CountContract', 'PUT_ContainsContract']

    

    p1 = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass, hashsetPUTs)
    
    subjects.append(p1)
    # End of HashSet

    # Dictionary
    sln = os.path.abspath('../ContractsSubjects/Dictionary/Dictionary.sln')
    projectName = 'DictionaryTest'
    testDebugFolder = '../ContractsSubjects/Dictionary/DictionaryTest/bin/Debug/'
    testDll = testDebugFolder + 'DictionaryTest.dll'
    testFileName = 'DictionaryContractTest.cs'
    testNamepace = 'Dictionary.Test'
    testClass = 'DictionaryContractTest'
    dictionaryPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_GetContract', 'PUT_SetContract',
                      'PUT_ContainsKeyContract', 'PUT_ContainsValueContract', 'PUT_CountContract']
    
    p2 = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,dictionaryPUTs)
    
    subjects.append(p2)
    # End of Dictionary

    # Queue
    sln = os.path.abspath('../ContractsSubjects/Queue/Queue.sln')
    projectName = 'QueueTest'
    testDebugFolder = '../ContractsSubjects/Queue/QueueTest/bin/Debug/'
    testDll = testDebugFolder + 'QueueTest.dll'
    testFileName = 'QueueContractTest.cs'
    testNamepace = 'Queue.Test'
    testClass = 'QueueContractTest'
    queuePUTs = ['PUT_EnqueueContract', 'PUT_DequeueContract',
                 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    p3 = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,queuePUTs )
    subjects.append(p3)
    
    # End Queue

    # ArrayList
    sln = os.path.abspath('../ContractsSubjects/ArrayList/ArrayList.sln')
    projectName = 'ArrayListTest'
    testDebugFolder = '../ContractsSubjects/ArrayList/ArrayListTest/bin/Debug/'
    testDll = testDebugFolder + 'ArrayListTest.dll'
    testFileName = 'ArrayListContractTest.cs'
    testNamepace = 'ArrayList.Test'
    testClass = 'ArrayListContractTest'
    arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract',
                     'PUT_GetContract', 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    #arrayListPUTs = ['PUT_ContainsKeyContract','PUT_ContainsValueContract','PUT_CountContract']
    p4 = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,arrayListPUTs)
    
    subjects.append(p4)

    #TODO: Add PUT fields to Problem 

    for prob in subjects:
        prob = p3
        #prob.puts = whatever i want
        runLearnPost(prob, prob.puts, prob.projectName , outputFileType, 1)
        #learnPostUpToK(prob,prob.puts[0],outputFileType,1)
        #Testing: just call learnUpToK
        sys.exit(0)
    # End ArrayList
