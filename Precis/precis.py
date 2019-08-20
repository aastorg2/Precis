import os
from os import sys, path
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


def learnPost(p,PUTName, outputFile):
    
    r0 = -1
    r1 = -1
    r2 = -1
    postK0 = PrecisFormula(BoolVal(True))
    postK1 = PrecisFormula(BoolVal(True))
    postK2 = PrecisFormula(BoolVal(True))
    simpPostK0 = PrecisFormula(BoolVal(True))
    simpPostK1 = PrecisFormula(BoolVal(True))
    simpPostK2 = PrecisFormula(BoolVal(True))

    #(postK2,simpPostK2,r2) = learnPostUpToK(p,PUTName, outputFile,2)
    #print("smallest post up to k == 2", postK2.toInfix())
    #sys.exit(0)
    
    (postK1,simpPostK1,r1) = learnPostUpToK(p,PUTName, outputFile,0)
    #print("smallest post up to k == 2", postK1.toInfix())
    #sys.exit(0)
   
    #(postK0,simpPostK0,r0) = learnPostUpToK(p,PUTName,outputFile,0)
    #print("simplified: ", PrecisFormula(precisSimplify(postK0.formulaZ3)).toInfix() )
    #print("smallest post up to k == 0", postK0.toInfix())
    #sys.exit(0)
    
    return (postK0,simpPostK0, r0, postK1,simpPostK1, r1 , postK2,simpPostK2, r2)
    
    

def learnPostUpToK(p,PUTName, outputFile, k):
    sygusExecutable = "Precis/Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "tempLocation"
    sygusFileName = "postcondition.sl"
    
    #assumes MSBuils.exe in path
    inst = Instrumenter("MSBuild.exe","./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")

    p.ExtractObservers(PUTName, outputFile)

    #returns list of base features
    baseFeatures: List[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allPostconditions = []
    allBaseFeatureVectors = []
    
    # FixMe: feature synthesis object shoul be initialized with base features and the feature vector should be updated
    featureSynthesizer = FeatureSynthesis(sygusExecutable,tempLocation,sygusFileName, baseFeatures)

    initFormula = PrecisFormula(BoolVal(False))
    inst.instrumentPost(p,initFormula , PUTName)
    rounds = 1
    while True:
        pex = Pex()
        
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(p, PUTName, baseFeatures)
        allBaseFeatureVectors.extend(baseFeatureVectors)

        featureSynthesizer.setBaseFeatureVector(baseFeatureVectors)
        derivedFeatures: List[PrecisFeature] = \
                featureSynthesizer.synthesizeFeatures() + \
                featureSynthesizer.GenerateDerivedFeatures()

        features: List[PrecisFeature] =  baseFeatures + derivedFeatures
        
        featurizer: Type[Featurizer] = Featurizer(derivedFeatures, baseFeatures, allBaseFeatureVectors)

        boolFeatures, boolFeatureIndices = featurizer.getBoolFeatures(features)
        boolFeatureVectors = featurizer.getBoolFeatureVectors(featurizer.completeFVs, boolFeatureIndices)
        #FixMe: initialize disjunctive learner with feature Synthesis Object
        disLearner = DisjunctiveLearner(featureSynthesizer)
        indices = []
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
            simplifiedPost = PrecisFormula(precisSimplify(postcondition.formulaZ3))
            return postcondition, simplifiedPost, rounds
        
        allPostconditions.append(postcondition.formula)
        rounds = rounds + 1

#todo: list of problems
def runLearnPost(p, putList,projectName,outputFile):
    #assert puts in putList in problem
    logger1.info("Problem: "+projectName+"\n")
    for PUTName in putList:
        # post = learnPost(p,PUTName, outputFile)
        logger1.info("PUT: "+PUTName+"\n")
        (postK0,simpPostK0,r0, postK1,simpPostK1,r1, postK2,simpPostK2,r2) = learnPost(p, PUTName, outputFile)
        logger1.info("postcondition k == 0\n "+ postK0.toInfix()+"\nrounds: "+str(r0)+"\n")
        logger1.info("simple   post k == 0\n "+ simpPostK0.toInfix()+"\nrounds: "+str(r0)+"\n")
        logger1.info("postcondition k == 1\n "+ postK1.toInfix()+"\nrounds: "+str(r1)+"\n")
        logger1.info("simple   post k == 1\n "+ simpPostK1.toInfix()+"\nrounds: "+str(r1)+"\n")
        logger1.info("postcondition k == 2\n "+ postK2.toInfix()+"\nrounds: "+str(r2)+"\n")
        logger1.info("simple   post k == 2\n "+ simpPostK2.toInfix()+"\nrounds: "+str(r2)+"\n")
        print("postcondition k == 0 ", postK0.toInfix(), "rounds: ", r0)
        print("simple   post k == 0 ", simpPostK0.toInfix(), "rounds: ", r0,"\n")
        print("postcondition k == 1 ", postK1.toInfix(), "rounds: ", r1)
        print("simple   post k == 1 ", simpPostK1.toInfix(), "rounds: ", r1,"\n")
        print("postcondition k == 2 ", postK2.toInfix(), "rounds: ", r2)
        print("simple   post k == 2 ", simpPostK2.toInfix(), "rounds: ", r2,"\n")
        
        implication = Implies(postK0.formulaZ3,postK1.formulaZ3)
        solver0 = Solver()
        solver0.add(Not(implication)) # check (not (postK0 => postK1)) is unsat
        check0 = solver0.check()
        #logger1.info("first check\n")
        #logger1.info(solver0.to_smt2()+"\n")
        logger1.info("Not(k0 -> k1)? "+ str(check0)+"\n")
        print("is it unsat?", check0 ) # if unsat, stop
        nextImplication = Implies(postK1.formulaZ3,postK2.formulaZ3) # check (not (postK1 => postK2)) is unsat
        solver1 = Solver()
        solver1.add(Not(nextImplication))
        check1 = solver1.check()
        logger1.info("Not(k1 -> k2)"+ str(check1)+"\n")
        print("is it unsat?", check1)
        nextNextImplication = Implies(postK0.formulaZ3,postK2.formulaZ3) # check (not (postK1 => postK2)) is unsat
        solver2 = Solver()
        solver2.add(Not(nextNextImplication))
        check2 = solver2.check()
        logger1.info("Not(k0 -> k2)"+ str(check2)+"\n")
        print("is it unsat?", check2)

def precisSimplify(postcondition):
        set_option(max_args = 10000000, max_lines = 1000000, max_depth = 10000000, max_visited = 1000000)
        set_option(html_mode=False)
        set_fpa_pretty(flag=False)
        
        #intVars = [ Int(var) for var in intVariables]
        #boolVars = [ Bool(var) for var in boolVariables]
    
        #declareInts = "\n".join([ "(declare-const " + var + " Int)" for var in intVariables ])
        #declareBools = "\n".join([ "(declare-const " + var + " Bool)" for var in boolVariables ])
        #stringToParse = "\n".join([declareInts,  declareBools, "( assert " + precondition + ")"])
    
        #logger = logging.getLogger("Framework.z3Simplify")
    
        #logger.info("############ z3 program")
        #logger.info("############ " + stringToParse)
    
        #expr = parse_smt2_string(stringToParse)
        
        g  = Goal()
        g.add(postcondition)
        
        works = Repeat(Then( 
        
        OrElse(Tactic('ctx-solver-simplify'),Tactic('skip')),
        
        # OrElse(Tactic('unit-subsume-simplify'),Tactic('skip')),
        # OrElse(Tactic('propagate-ineqs'),Tactic('skip')),
        # OrElse(Tactic('purify-arith'),Tactic('skip')),
        # OrElse(Tactic('ctx-simplify'),Tactic('skip')),
        # OrElse(Tactic('dom-simplify'),Tactic('skip')),
        # OrElse(Tactic('propagate-values'),Tactic('skip')),
        
        OrElse(Tactic('simplify'),Tactic('skip')),
        
        # OrElse(Tactic('aig'),Tactic('skip')),
        # OrElse(Tactic('degree-shift'),Tactic('skip')),
        # OrElse(Tactic('factor'),Tactic('skip')),
        # OrElse(Tactic('lia2pb'),Tactic('skip')),
        # OrElse(Tactic('recover-01'),Tactic('skip')),
        
        OrElse(Tactic('elim-term-ite'),Tactic('skip')), #must to remove ite
        
        # OrElse(Tactic('injectivity'),Tactic('skip')),
        # OrElse(Tactic('snf'),Tactic('skip')),
        # OrElse(Tactic('reduce-args'),Tactic('skip')),
        # OrElse(Tactic('elim-and'),Tactic('skip')),
        # OrElse(Tactic('symmetry-reduce'),Tactic('skip')),
        # OrElse(Tactic('macro-finder'),Tactic('skip')),
        # OrElse(Tactic('quasi-macros'),Tactic('skip')),
        
        Repeat(OrElse(Tactic('split-clause'),Tactic('skip'))),
        ))
        #works1 = Tactic('simplify')    

        result = works(g)
        #result = works1(g)
        # split_all = 

        # print str(result)
        # result = [[ "d1", "d2", "d3"], #= conjunct && conjunct
        #           [ "d4", "d5", "d6"]]
        
        #remove empty subgoals and check if resultant list is empty.
        result = filter(None, result)
        if not result:
            return "true" 
        #return result
        
        completeConjunct = []
        for conjunct in result: 
            completeDisjunct = []
            for disjunct in conjunct:
                    completeDisjunct.append(disjunct)
                    
            completeConjunct.append(And(completeDisjunct) )
        
        simplifiedPrecondition = Or(completeConjunct)
        
        #simplifiedPrecondition = simplifiedPrecondition.replace("Not", " ! ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("False", " false ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("True", " true ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("\n", "  ")
        return simplifiedPrecondition


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

    ################ Stack
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

    #stackPUTs = ['PUT_PushContract']
    p = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    
    
    #runLearnPost(p,stackPUTs,projectName, outputFile)
    
    ################ Stack

    ################ HashSet
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
    hashsetPUTs = ['PUT_AddContract']    
    runLearnPost(p1,hashsetPUTs,projectName,outputFile)

    ################ HashSet


    ################ Dictionary

    sln = os.path.abspath('../ContractsSubjects/Dictionary/Dictionary.sln')
    projectName =  'DictionaryTest'
    testDebugFolder = '../ContractsSubjects/Dictionary/DictionaryTest/bin/Debug/'
    testDll = testDebugFolder + 'DictionaryTest.dll'
    testFileName = 'DictionaryContractTest.cs' 
    testNamepace = 'Dictionary.Test'
    testClass = 'DictionaryContractTest'
    dictionaryPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_GetContract', 'PUT_SetContract','PUT_ContainsKeyContract','PUT_ContainsValueContract','PUT_CountContract'] 
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    p2 = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    outputFile = os.path.abspath('./typesOM.txt')
    
    #runLearnPost(p2,dictionaryPUTs, projectName, outputFile)

    ################ Dictionary

    ################ Queue
    sln = os.path.abspath('../ContractsSubjects/Queue/Queue.sln')
    projectName =  'QueueTest'
    testDebugFolder = '../ContractsSubjects/Queue/QueueTest/bin/Debug/'
    testDll = testDebugFolder + 'QueueTest.dll'
    testFileName = 'QueueContractTest.cs' 
    testNamepace = 'Queue.Test'
    testClass = 'QueueContractTest'
    queuePUTs = ['PUT_EnqueueContract', 'PUT_DequeueContract', 'PUT_PeekContract', 'PUT_CountContract','PUT_ContainsContract'] 
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    p3 = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    outputFile = os.path.abspath('./typesOM.txt')
    
    #runLearnPost(p3,queuePUTs,projectName,outputFile)

    ################ Queue

    ################ ArrayList
    sln = os.path.abspath('../ContractsSubjects/ArrayList/ArrayList.sln')
    projectName =  'ArrayListTest'
    testDebugFolder = '../ContractsSubjects/ArrayList/ArrayListTest/bin/Debug/'
    testDll = testDebugFolder + 'ArrayListTest.dll'
    testFileName = 'ArrayListContractTest.cs' 
    testNamepace = 'ArrayList.Test'
    testClass = 'ArrayListContractTest'
    arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract','PUT_InsertContract', 'PUT_SetContract','PUT_GetContract','PUT_ContainsContract','PUT_IndexOfContract','PUT_LastIndexOfContract','PUT_CountContract'] 
    #PUTName = 'PUT_PushContract'
    #PUTName = 'PUT_PopContract'
    #arrayListPUTs = ['PUT_ContainsKeyContract','PUT_ContainsValueContract','PUT_CountContract'] 
    p4 = Problem(sln, projectName, testDebugFolder, testDll, testFileName, testNamepace, testClass)
    outputFile = os.path.abspath('./typesOM.txt')
    
    #runLearnPost(p4,arrayListPUTs,projectName,outputFile)

    ################ ArrayList
