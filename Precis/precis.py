import os
from os import sys, path
import time
from z3 import *
from Data.problem import Problem
from Data.precis_feature import PrecisFeature
from Data.precis_formula import PrecisFormula
from Data.feature_vector import FeatureVector
from Teachers.pex import Pex
from Teachers.instrumenter import Instrumenter
from Learners.feature_synthesis import FeatureSynthesis
from Learners.houdini import Houdini
from Learners.disjunctive_learner import DisjunctiveLearner
from Learners.sygus2 import SygusDisjunctive
from Learners.houdini import Houdini
from featurizer import Featurizer
import shutil
from typing import List, Tuple, Type
import logging
import evaluation

import Teachers.command_runner
import operator

print("In precis.py: \n" + str(sys.path))
#learning function 1 --- based decision tree
def learnPostUpToK(p, PUTName, outputFile, k, destinationOfTests):
    sygusExecutable = "./Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "../tempLocation"
    sygusFileName = "postcondition.sl"
    #assumes MSBuils.exe in path
    inst = Instrumenter("MSBuild.exe", "../Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    p.ExtractObservers(PUTName, outputFile, "precis")
    
    # returns list of base features
    baseFeatures: Tuple[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allPostconditions = []
    allBaseFeatureVectors = []

    synthesizer = FeatureSynthesis(sygusExecutable, tempLocation, sygusFileName)
    currentPostcondition = PrecisFormula(BoolVal(False))
    inst.instrumentPost(p, currentPostcondition, PUTName)
    rounds = 1
    totalPexTime = 0.0
    totalLearningTime = 0.0
    while True:
        print("starting round: " + str(rounds))
        pex = Pex()
        
        startTimePex = time.time()
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(p, PUTName, baseFeatures)
        pexTime = time.time() - startTimePex
        totalPexTime += pexTime
        print("pex time: " + str(totalPexTime))
        print("learning time: "+ str(totalLearningTime))

        evaluation.copyTestFilesToEvaluationDir(pex.testsLocation,destinationOfTests, rounds)
        #sys.exit(0)
        allBaseFeatureVectors.extend(baseFeatureVectors)

        if all(baseFeatureVectors[i].testLabel for i in range(0, len(baseFeatureVectors))):
            print("found it")
            simplifiedPost = PrecisFormula(currentPostcondition.precisSimplify())
            return currentPostcondition, simplifiedPost, rounds, totalPexTime, totalLearningTime, len(allBaseFeatureVectors)

        if rounds == 20:
            print("BAD!")
            simplifiedPost = PrecisFormula(currentPostcondition.precisSimplify())
            return currentPostcondition, simplifiedPost, rounds, totalPexTime, totalLearningTime, len(allBaseFeatureVectors)

        if len(baseFeatureVectors) == 0:
            logger1.info("process TERMINATED with TG not generating any test! DEBUG ME!\n")
            simplifiedPost = PrecisFormula(currentPostcondition.precisSimplify())
            return currentPostcondition, simplifiedPost, rounds , totalPexTime, totalLearningTime, len(allBaseFeatureVectors)

        intBaseFeatures, boolBaseFeatures = Featurizer.getIntAndBoolFeatures(baseFeatures)
        disLearner = DisjunctiveLearner(synthesizer)
        logger1.info("#############\nRound: "+str(rounds)+"\n")
        # Learning function
        startLearningTime = time.time()
        s = Solver()
        postcondition = disLearner.learn3( k, intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors, (), s,"root")
        learningTime = time.time() - startLearningTime
        totalLearningTime += learningTime

        logger1.info("Unsimplified post:\n\n"+ postcondition.toInfix()+"\n")
        
        print("unsimplified post "+ postcondition.toInfix())
        print("")
        print("Simplified post:\n\n"+ PrecisFormula(postcondition.precisSimplify()).toInfix() )
        # assumes ms build in path
        #inst = Instrumenter(
        #    "MSBuild.exe", "./Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
        inst.instrumentPost(p, postcondition, PUTName)
        
        currentPostcondition = PrecisFormula(postcondition.formulaZ3)
        allPostconditions.append(postcondition.formulaZ3)
        rounds = rounds + 1



def runLearnPost(p, putList, projectName, outputFile, k ):
    #assert puts in putList in problem
    logger1.info("Problem: "+projectName+"\n")
    
    for PUTName in putList:
        #delete directory where pex initially stores tests -> we don't want old test seeding pex
        if os.path.exists(p.testDebugFolder):
            shutil.rmtree(p.testDebugFolder)

        logger1.info("PUT: "+PUTName+"\n")
        results = []
        for i in range(0, k+1):
            
            locationOfTests = evaluation.createDirectoryForTests("../../evaluation", p.projectName, PUTName,"Case"+str(i))
            assert(locationOfTests != None)
            
            print(locationOfTests)
            #sys.exit(0)

            logger1.info("=====\nCase: k == "+str(i)+"\n")
            (post, simplePost, rounds, pexTime, learnTime, totalSamples) = learnPostUpToK(p, PUTName, outputFile, i, locationOfTests)
            logger1.info("===== Final Result for "+PUTName +"\n")
            logger1.info("postcondition k == "+str(i)+"\n" +
                        post.toInfix()+"\nrounds: " + str(rounds) + "\n")
            logger1.info("simplified post k == " + str(i) + "\n"+
                        simplePost.toInfix())
            logger1.info("pex time: "+str(pexTime)+"\n")
            logger1.info("learn time: "+str(learnTime)+"\n")
            logger1.info("Samples: "+str(totalSamples)+"\n")
            
            results.append((post, simplePost, rounds))
            
            if i == 2:
                implication2 = Implies(results[i-2][0].formulaZ3, results[i][0].formulaZ3)
                solver2 = Solver()
                # check (not (postK0 => postK1)) is unsat
                solver2.add(Not(implication2))
                check2 = solver2.check()
                logger1.info("Not(k"+str(i-2)+" -> k" + str(i) +")? " + str(check2)+"\n")

                implication3 = Implies(results[i-1][0].formulaZ3, results[i][0].formulaZ3)
                solver3 = Solver()
                solver3.add(Not(implication3))
                check3 = solver3.check()
                logger1.info("Not(k"+str(i-1)+" -> k" + str(i) +")? " + str(check3)+"\n")

            
            elif i == 1:
                implication = Implies(results[i-1][0].formulaZ3, results[i][0].formulaZ3)
                solver = Solver()
                # check (not (postK0 => postK1)) is unsat
                solver.add(Not(implication))
                check = solver.check()
                logger1.info("Not(k"+str(i-1)+" -> k" + str(i) +")? " + str(check)+"\n")

                implication4 = Implies( results[i][0].formulaZ3,results[i-1][0].formulaZ3)
                solver4 = Solver()
                # check (not (postK0 => postK1)) is unsat
                solver4.add(Not(implication4))
                check4 = solver.check()
                logger1.info("Not(k"+str(i)+" -> k" + str(i-1) +")? " + str(check4)+"\n")

            
def runLearnPostTest(p, putList, projectName, outputFile, k):
    #assert puts in putList in problem
    logger1.info("Problem: "+projectName+"\n")
    
    # delete old pex files first
    if os.path.exists(...):
        shutil.rmtree(p.testDebugFolder)

    for PUTName in putList:
        
        locationOfTests = evaluation.createDirectoryForTests("../evaluation", p.projectName, PUTName,"Case"+str(k))
        assert(locationOfTests != None)
        
        logger1.info("PUT: "+PUTName+"\n")
        results = []
        
        logger1.info("=====\nCase: k == "+str(k)+"\n")
        (post, simplePost, rounds, pexTime, learnTime, totalSamples)  = learnPostUpToK(p, PUTName, outputFile,k,locationOfTests)
        logger1.info("===== Final Result for "+PUTName +"\n")
        logger1.info("postcondition k == "+str(k)+"\n" +
                    post.toInfix()+"\nrounds: " + str(rounds) + "\n")
        logger1.info("simplified post k == " + str(k) + "\n"+
                        simplePost.toInfix())
        logger1.info("pex time: "+str(pexTime)+"\n")
        logger1.info("learn time: "+str(learnTime)+"\n")
        logger1.info("Samples: "+str(totalSamples)+"\n")

#learning function 2 --- based on synthesis and  decision tree
def SynthTightDT(p, PUTName, outputFile, destinationOfTests, maxK):
    sygusExecutable = "./Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "../tempLocation"
    sygusFileName = "postcondition.sl"
    #assumes MSBuils.exe in path
    inst = Instrumenter("MSBuild.exe", "../Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    p.ExtractObservers(PUTName, outputFile, "precis")
    
    # returns list of base features
    baseFeatures: Tuple[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allPostconditions = []
    allBaseFeatureVectors = []

    synthesizer = FeatureSynthesis(sygusExecutable, tempLocation, sygusFileName)
    currentStringTree = "false"
    inst.instrumentPostString(p, currentStringTree, PUTName)
    
    rounds = 1
    totalPexTime = 0.0
    totalLearningTime = 0.0
    currentPostcondition = None
    candidatePostcondition = None
    simplifiedPost =""
    print(p, PUTName, outputFile, destinationOfTests)
    dtWithSynthesisLearningTime = 0.0
    while True:
        print("starting round: " + str(rounds))
        #For this kind of learner, consider optimizing by generating fixed templates once. Only call sygus per round.
        pex = Pex()
            
        
        startTimePex = time.time()
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(p, PUTName, baseFeatures)
        pexTime = time.time() - startTimePex
        totalPexTime = totalPexTime + pexTime
        
        #copy tests
        evaluation.copyTestFilesToEvaluationDir(pex.testsLocation, destinationOfTests, rounds)

        if all(baseFeatureVectors[i].testLabel for i in range(0, len(baseFeatureVectors))):
            #In the first round, 
            print("found it")
            simplifiedPost = PrecisFormula(candidatePostcondition.precisSimplify()).toInfix()
            return candidatePostcondition, candidatePostcondition.toInfix(), simplifiedPost, rounds, totalPexTime, totalLearningTime, len(allBaseFeatureVectors)
            #break
        if rounds == 16:
            print("did not find it - Max Rounds")
            break
        
        print("Pex Finished")
        allBaseFeatureVectors.extend(baseFeatureVectors)
        
        intBaseFeatures, boolBaseFeatures = Featurizer.getIntAndBoolFeatures(baseFeatures)
        
        (intBaseFeatVectors, boolBaseFeatVectors) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors)
        
        disLearner = DisjunctiveLearner(synthesizer)
        ss = Solver()
        allBoolFeats=set()
        postSmt = "true"
        startDtLearningTime = time.time()
        postcondition, allBoolFeats, postSmt = disLearner.learn4( 2, intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors, (), ss,"root")
        endDtTime = time.time() - startDtLearningTime 
        dtWithSynthesisLearningTime = dtWithSynthesisLearningTime + endDtTime
        print("++++++++++++++++++++++")
        print(PrecisFormula(postcondition.precisSimplify()).toInfix())
        allBoolFeatsList = list(allBoolFeats)
        #print(intBaseFeatVectors, boolBaseFeatVectors)
        #print(intBaseFeatures, boolBaseFeatures)
        allBoolFeatsDerivList = [f for f in allBoolFeatsList if f not in boolBaseFeatures ]
        #derivFeats = synthesizeUniqueFeatures(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors, [],synthesizer)
        allBoolFeatsDerivList = sorted( allBoolFeatsDerivList, key=lambda pf: len(pf.varName))
        derivFeats = tuple(allBoolFeatsDerivList)
        
        derivFeatVectors: List[FeatureVector] = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeatures+boolBaseFeatures,allBaseFeatureVectors)

        boolFvs = Featurizer.mergeFeatureVectors(boolBaseFeatVectors,derivFeatVectors)
        boolFeatures = boolBaseFeatures + derivFeats
        atoms = generateAtomPredicates(len(boolFeatures))
        strBoolFvs = [ fv.getStrFeatureVectorsOnly().lower().replace("(","").replace(")","").split(", ") for fv in boolFvs ]
        postSmtAtom  = replaceInfixToAtoms(postSmt,atoms,boolFeatures)
        
        houdini = Houdini()
        (conjunct, indexes) = houdini.learnHoudiniString(atoms, strBoolFvs)
        (conjunctPrecis, idxs, conjuncts) = houdini.learn4(boolFeatures, boolFvs, "root")

        sygusConjunct = '(and ' + ' '.join(conjunct) + ')'
        #no way to know if feature in boolFeatures should be negated
        #regularConjunct = replace(sygusConjunct, atoms, boolFeatures)
        (condAtoms,strCondBoolFvs, universallyTrue) = removeUniversallyTrueFalse(atoms, strBoolFvs)
        
        condPostSmtAtom = removeTopMostCommonConjunct(universallyTrue,postSmtAtom)
        #condPostSmtAtom = "true"
        print("tree from dt w/ synthesis:\n "+ condPostSmtAtom)
        k = 1
        config = False
        #currentBestTreeAtK = condPostSmtAtom
        currentBestTreeAtK = 'true'
        currentBestTree = None
        stringTree = ""
        stringTreeReplaced = ""
        timePerK = []
        while True and k <= maxK:
            if k == maxK:
                logger1.info("Reached max k: "+ str(maxK)+ " for round: "+ str(rounds)+ " in problem: "+ PUTName)

            print("solving for k="+str(k))

            solver1 = SygusDisjunctive(
                            atoms if config else condAtoms,
                            strBoolFvs if config else strCondBoolFvs,
                            k=k,
                            cdt=currentBestTreeAtK)
            startKExecTime = time.time()
            output_tree = solver1.run_sygus()
            kExecTime = time.time() - startKExecTime
            timePerK.append( (k, kExecTime) )
            totalLearningTime = totalLearningTime + kExecTime
            
            if output_tree != None: # phase1: exhaust trees at k
                currentBestTreeAtK = output_tree.parseWithHoudiniWithPruning(condAtoms,strCondBoolFvs)
                currentBestTree = output_tree
            elif currentBestTree != None: #phase 2: check if there is a better tree before moving on to k+1. Note however when currentBestTree is None, then it must mean 
                #there was no tree of depth k so will skip checking at k+1
                # at this point, currentBestTreeAtK has the best tree of depth k. So now, we check if there exist a better tree of depth k+1
                copy2StrBoolFvs = list(strBoolFvs)
                copyboolFvs = list (boolFvs)
                s1 = Solver()
                print("best tree at depth k")
                print("disjunctive sygus format:\n"+currentBestTreeAtK)
                print("z3 simplified:\n"+PrecisFormula(currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy2StrBoolFvs, copyboolFvs, s1, "root").precisSimplify()).toInfix()+"\n") # destroys copy2StrBoolFvs
                
                print("checking if there exist a tree at k+1 depth that is tigher?")
                solver2 = SygusDisjunctive(
                            atoms if config else condAtoms,
                            strBoolFvs if config else strCondBoolFvs,
                            k=(k+1),
                            cdt=currentBestTreeAtK)
                startKExecTime = time.time()
                output_tree = solver2.run_sygus()
                kExecTime = time.time() - startKExecTime
                timePerK.append( (k, kExecTime) )
                totalLearningTime = totalLearningTime + kExecTime
                if output_tree != None:
                    copy3StrBoolFvs = list(strBoolFvs)
                    copy2boolFvs = list (boolFvs)
                    print("Yes, best tree at k+1")
                    currentBestTreeAtK = output_tree.parseWithHoudiniWithPruning(condAtoms,strCondBoolFvs)
                    print("disjunctive sygus format:\n"+currentBestTreeAtK)
                    print("z3 simplified:\n"+PrecisFormula(output_tree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy3StrBoolFvs, copy2boolFvs, s1, "root").precisSimplify()).toInfix()+"\n")# destroys copy3StrBoolFvs
                    currentBestTree = output_tree
                    k = k + 1
                else:
                    break
            else:# this is hit when we have a conjunctive case
                print("there is no disjunctive formula")
                break

        
        print("round: "+str(rounds))
        for idx in range(0, len(timePerK)):
            print("k= "+str(timePerK[idx][0]) +" " +str(timePerK[idx][1]))
        
        listOfTimesPerK = [entry[1] for entry in timePerK]
        print("sygu disjunc. learning time in this round: "+ str(sum(map(float, listOfTimesPerK))) )
        print("sygu disjunc. learning time across all rounds: "+ str( totalLearningTime))
        print("dt w/ synthesis time in this round: "+str(endDtTime))
        print("dt w/ synthesis across all rounds "+ str(dtWithSynthesisLearningTime))
        totalLearningTime = totalLearningTime + dtWithSynthesisLearningTime
        print("total learning time (all rounds): "+ str(totalLearningTime))
        print("Total pex time: "+str(totalPexTime))

        if currentBestTree != None: # this is only true when there are no disjunctive concept and the tighest post is conjunctive
            copyStrBoolFvs = list(strBoolFvs)
            stringTree = currentBestTree.parseWithHoudini(atoms, strBoolFvs) #this call detroys strBoolFvs
            stringTreeReplaced = replace(stringTree, atoms, boolFeatures)
            s = Solver()
            logger1.info("Final Tree ====")
            logger1.info(f"Round: {rounds}")
            candidatePostcondition = currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copyStrBoolFvs, boolFvs, s, "root")
        else:
            stringTreeReplaced = PrecisFormula(conjunctPrecis.precisSimplify()).toInfix() #Debugging
            candidatePostcondition = conjunctPrecis

        strCandidatePostCondition = PrecisFormula(candidatePostcondition.precisSimplify()).toInfix()
        inst.instrumentPostString(p, strCandidatePostCondition, PUTName)
        rounds = rounds + 1
        
def SynthTightDT2(p, PUTName, outputFile, destinationOfTests, maxK):
    sygusExecutable = "./Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "../tempLocation"
    sygusFileName = "postcondition.sl"
    #assumes MSBuils.exe in path
    inst = Instrumenter("MSBuild.exe", "../Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    p.ExtractObservers(PUTName, outputFile, "precis")
    
    # returns list of base features
    baseFeatures: Tuple[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allPostconditions = []
    allBaseFeatureVectors = []

    synthesizer = FeatureSynthesis(sygusExecutable, tempLocation, sygusFileName)
    currentStringTree = "false"
    inst.instrumentPostString(p, currentStringTree, PUTName)
    
    rounds = 1
    totalPexTime = 0.0
    totalLearningTime = 0.0
    currentPostcondition = None
    candidatePost = None
    simplifiedPost =""
    print(p, PUTName, outputFile, destinationOfTests)
    dtWithSynthesisLearningTime = 0.0

    intBaseFeatures, boolBaseFeatures = Featurizer.getIntAndBoolFeatures(baseFeatures)
    templateFeats = synthesizer.GenerateDerivedFeatures(intBaseFeatures, boolBaseFeatures) 
    
    newCount = None
    oldCount = None
    precisFeat = None
    # for intFeat in intBaseFeatures:
    #     if intFeat.varName == "New_dCount":
    #         newCount = intFeat
    #     if intFeat.varName == "Old_dCount":
    #         oldCount = intFeat
    # if newCount != None and oldCount != None:
    #     exprMinus = oldCount.varZ3 - IntVal(1)
    #     exprEq = newCount.varZ3 == exprMinus
    #     print(exprEq)
    #     precisFeat = PrecisFeature(True, str(exprEq), str(exprEq.sort()), None, exprEq)
    # if precisFeat != None:
    #     templateFeats = templateFeats + (precisFeat,)

    while True:
        print("============================================================================= starting round: " + str(rounds))
        #For this kind of learner, consider optimizing by generating fixed templates once. Only call sygus per round.
        pex = Pex()
            
        
        startTimePex = time.time()
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(p, PUTName, baseFeatures)
        pexTime = time.time() - startTimePex
        totalPexTime = totalPexTime + pexTime
        
        #copy tests
        evaluation.copyTestFilesToEvaluationDir(pex.testsLocation, destinationOfTests, rounds)

        if all(baseFeatureVectors[i].testLabel for i in range(0, len(baseFeatureVectors))):
            #In the first round, 
            print("found it")
            simplifiedPost = PrecisFormula(candidatePost.precisSimplify()).toInfix()
            return candidatePost, candidatePost.toInfix(), simplifiedPost, rounds, totalPexTime, totalLearningTime, len(allBaseFeatureVectors)
            #break
        if rounds == 16:
            print("did not find it - Max Rounds")
            break
        
        print("Pex Finished")
        allBaseFeatureVectors.extend(baseFeatureVectors)
        
        (intBaseFeatVectors, boolBaseFeatVectors) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors)
        
        
        synthFeats = synthesizer.synthesizeFeatures(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors)
        uniqueSynthFeats = tuple([f for f in synthFeats if f not in templateFeats])
        
        derivFeats = templateFeats + uniqueSynthFeats
        derivFeatVecs = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeatures+boolBaseFeatures,allBaseFeatureVectors)
        # will have to change order: boolBaseFeatures at the end, while deriv at the beginning.
        #boolFeats = boolBaseFeatures + derivFeats
        boolFeats =  derivFeats + boolBaseFeatures
        #boolFeatVecs = Featurizer.mergeFeatureVectors(boolBaseFeatVectors, derivFeatVecs)
        boolFeatVecs = Featurizer.mergeFeatureVectors(derivFeatVecs, boolBaseFeatVectors)
        


        k = 1
        config = False
        #currentBestTreeAtK = condPostSmtAtom
        currentBestTreeAtK = 'true'
        currentBestTree = None
        stringTree = ""
        stringTreeReplaced = ""
        timePerK = []
        houdini = Houdini(intBaseFeatures, boolBaseFeatures, intBaseFeatVectors, boolBaseFeatVectors, derivFeats, synthesizer)
        
        conditionalFeats,conditionalFvs,alwaysTrue = removeUniversallyTrueFalse(boolFeats, boolFeatVecs) 
        #conditionalFeats = boolFeats 
        #conditionalFvs = boolFeatVecs 
        withSynth = False
        synthesizedFeatures = ()
        while True and k <= maxK:
            featWithSynt = conditionalFeats
            fvWithSynth = conditionalFvs
            
            if k == maxK:
                logger1.info("Reached max k: "+ str(maxK)+ " for round: "+ str(rounds)+ " in problem: "+ PUTName)

            print("=================================================== solving for k="+str(k))
            if len(synthesizedFeatures) > 0:
                withSynth = True
                featWithSynt = conditionalFeats + synthesizedFeatures
                synthFvs = Featurizer.generateDerivedFeatureVectors(synthesizedFeatures,intBaseFeatures+boolBaseFeatures, allBaseFeatureVectors)
                fvWithSynth = Featurizer.mergeFeatureVectors(conditionalFvs, synthFvs)
            
            solver1 = SygusDisjunctive(
                            conditionalFeats if not withSynth else featWithSynt,
                            conditionalFvs if not withSynth else fvWithSynth,
                            k=k,
                            cdt=currentBestTreeAtK)
            startKExecTime = time.time()
            output_tree = solver1.run_sygus()
            kExecTime = time.time() - startKExecTime
            timePerK.append( (k, kExecTime) )
            totalLearningTime = totalLearningTime + kExecTime
            
            if output_tree != None: # phase1: exhaust trees at k
                print("++++++++++++++ tree root: "+ output_tree.data.varName)
                currentBestTreeAtK, currentTighterPost, synthFeatures = houdini.houdiniSynthesis(output_tree, featWithSynt, fvWithSynth, "root")
                if len(synthFeatures)> 0:
                    synthesizedFeatures = addIfNotThereAlready(synthesizedFeatures, synthFeatures)
                    #updating global state
                    houdini.derivBoolFeats = addIfNotThereAlready(houdini.derivBoolFeats , synthesizedFeatures)
                    templateFeats = addIfNotThereAlready(templateFeats,synthesizedFeatures)
                    
                currentBestTree = output_tree

            
            elif currentBestTree != None: #phase 2: check if there is a better tree before moving on to k+1. Note however when currentBestTree is None, then it must mean 
                #there was no tree of depth k so will skip checking at k+1
                # at this point, currentBestTreeAtK has the best tree of depth k. So now, we check if there exist a better tree of depth k+1
                #copy2StrBoolFvs = list(strBoolFvs)
                #copyboolFvs = list (boolFvs)
                
                print("best tree at depth k")
                print("disjunctive sygus format:\n"+currentBestTreeAtK)
                #print("z3 simplified:\n"+PrecisFormula(currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy2StrBoolFvs, copyboolFvs, s1, "root").precisSimplify()).toInfix()+"\n") # destroys copy2StrBoolFvs
                
                print("checking if there exist a tree at k+1 depth that is tigher?")
                solver2 = SygusDisjunctive(
                            conditionalFeats if not withSynth else featWithSynt,
                            conditionalFvs if not withSynth else fvWithSynth,
                            k=(k+1),
                            cdt=currentBestTreeAtK)
                startKExecTime = time.time()
                output_tree = solver2.run_sygus()
                kExecTime = time.time() - startKExecTime
                timePerK.append( (k, kExecTime) )
                totalLearningTime = totalLearningTime + kExecTime
                if output_tree != None:
                    #copy3StrBoolFvs = list(strBoolFvs)
                    #copy2boolFvs = list (boolFvs)
                    print("Yes, tighter tree at k+1")
                    currentBestTreeAtK, currentTighterPost, synthFeatures = houdini.houdiniSynthesis(output_tree, featWithSynt, fvWithSynth, "root")
                    if len(synthFeatures)> 0:
                        synthesizedFeatures = addIfNotThereAlready(synthesizedFeatures, synthFeatures)
                        #updating global state 
                        houdini.derivBoolFeats = addIfNotThereAlready(houdini.derivBoolFeats , synthesizedFeatures)
                        templateFeats = addIfNotThereAlready(templateFeats,synthesizedFeatures)
                    
                    print("disjunctive sygus format:\n"+currentBestTreeAtK)
                    print("post precis: \n"+ PrecisFormula(currentTighterPost.precisSimplify()).toInfix())
                    #print("z3 simplified:\n"+PrecisFormula(output_tree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy3StrBoolFvs, copy2boolFvs, s1, "root").precisSimplify()).toInfix()+"\n")# destroys copy3StrBoolFvs
                    currentBestTree = output_tree
                    k = k + 1
                else:
                    break
            else:# this is hit when we have a conjunctive case
                print("there is no disjunctive formula")
                break

        
        print("round: "+str(rounds))
        for idx in range(0, len(timePerK)):
            print("k= "+str(timePerK[idx][0]) +" " +str(timePerK[idx][1]))
        
        listOfTimesPerK = [entry[1] for entry in timePerK]
        print("sygu disjunc. learning time in this round: "+ str(sum(map(float, listOfTimesPerK))) )
        print("sygu disjunc. learning time across all rounds: "+ str( totalLearningTime))
        print("total learning time (all rounds): "+ str(totalLearningTime))
        print("Total pex time: "+str(totalPexTime))
        
        if currentBestTree != None: # this is only false when there are no disjunctive concept and the tighest post is conjunctive
            #copyStrBoolFvs = list(strBoolFvs)
            #stringTree = currentBestTree.parseWithHoudini(atoms, strBoolFvs) #this call detroys strBoolFvs
            #stringTreeReplaced = replace(stringTree, atoms, boolFeatures)
            #s = Solver()
            logger1.info("Final Tree ====")
            logger1.info(f"Round: {rounds}")
            #candidatePostcondition = currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copyStrBoolFvs, boolFvs, s, "root")
            
            smtCandidatePost, candidatePost, synthFeatures = houdini.houdiniSynthesis(currentBestTree, featWithSynt, fvWithSynth, "root")
            # learn6 does not return predicates that are always false
            #simplifiedPost = PrecisFormula(candidatePost.precisSimplify()).toInfix()
            print("learned candidate post(before simplify): "+ candidatePost.toInfix())
            candidatePost = PrecisFormula(candidatePost.precisSimplify())
            print()
            conjunctPrecis, indices, conjuncts = houdini.learn6(boolFeats, boolFeatVecs,"root")
            conjunctZ3simple = conjunctPrecis.precisSimplify()
            candidatePost = PrecisFormula(And(conjunctZ3simple,candidatePost.formulaZ3))
            #smtCandidatePost, candidatePost, synthFeatures = houdini.houdiniSynthesis(currentBestTree, boolFeats, boolFeatVecs, "root")

        else:
            print("no disjunctive formula")
            conjunctPrecis, indices, conjuncts = houdini.learn5(boolFeats, boolFeatVecs,"root")
            #stringTreeReplaced = PrecisFormula(conjunctPrecis.precisSimplify()).toInfix() #Debugging
            candidatePost = conjunctPrecis

        strCandidatePost = PrecisFormula(candidatePost.precisSimplify()).toInfix()
        print("candidate post: "+ strCandidatePost)
        inst.instrumentPostString(p, strCandidatePost, PUTName)
        rounds = rounds + 1    
        

def runSynthTightDT(p, putList, projectName, outputFile):
    logger1.info("Problem: "+projectName+"\n")

    for putName in putList:
        ## location to store tests
        locationOfTests = evaluation.createDirectoryForTestsWithoutCase("../evaluation2", projectName, putName)
        assert(locationOfTests != None)

        logger1.info("PUT: "+putName+"\n")
        (currentPost, learnedPostStr, simplifiedPostStr, rounds, pexTime, learnTime, totalSamples) = SynthTightDT2(p, putName, outputFile, locationOfTests , 20)
        print("learnerd post:")
        print(learnedPostStr +"\n")
        print("simplified post:")
        print(simplifiedPostStr+"\n")

        logger1.info("===== Final Result for "+putName +"\n")
        logger1.info("postcondition: \n" +
                    learnedPostStr+"\nrounds: " + str(rounds) + "\n")
        logger1.info("simplified post: " + "\n"+
                        simplifiedPostStr)
        logger1.info("pex time: "+str(pexTime)+"\n")
        logger1.info("learn time: "+str(learnTime)+"\n")
        logger1.info("Samples: "+str(totalSamples)+"\n")
        #delete directory where pex initially stores tests -> we don't want old test seeding pex
        if os.path.exists(p.testDebugFolder):
            shutil.rmtree(p.testDebugFolder)
        #f = open("testingData.txt", "a")
        #f.write("PUT: "+putName)
        #f.write("simplified Post")
        #f.write(simplifiedPostStr)
        #f.close()
        """
        currentPost2, learnedPostStr2, simplifiedPostStr2 = SynthTightDT(p, putName, outputFile, locationOfTests ,2)
        print("learnerd post:")
        print(learnedPostStr2+"\n")
        print("simplified post:")
        print(simplifiedPostStr2+"\n")

        implication = Implies(currentPost.formulaZ3, currentPost2.formulaZ3)
        solver = Solver()
        solver.add(Not(implication))
        print("results: " +solver.check())
        """


def addIfNotThereAlready(features, synthFeats):
    featRet = features
    for f in synthFeats:
        if  f not in features:
            featRet =  featRet + (f,)
    return featRet

def removeTopMostCommonConjunct(universallyTrue, postcondition):
    import re

    if not "ite" in postcondition:
        return "true"
    condPost = ""
    # '\(and \(and (?:(?:\(not cond[0-9]+\)\s*|cond[0-9]+\s*)*|true)\)' --> original workin regex
    #regPattern = "(\(and \(and (\(not cond[0-9]+\)\s*|cond[0-9]+\s*)*|true\))"
    regPattern = '\(and \(and (?:(?:\(not cond[0-9]+\)\s*|cond[0-9]+\s*)*|true)\)'
    matches = re.findall(regPattern, postcondition)
    if len(matches) > 0:
        condPost = postcondition.replace(matches[0],"(and " )

    return condPost

#refactor such you always overwrite a list of list of feature vectors.
def removeUniversallyTrueFalse(boolFeats, boolFvs ):
    workList = {key: True for key in range(0, len(boolFeats))}
    remainingCondTruePredicates = tuple()
    idxsValuesToKeep = []
    idxsToRemove = []
    init = ""
    strCondTrueFvs=[]
    universallyTrue=[]
    for idx in range(0, len(boolFeats)): # no need to start from the end :Refactor
        # we just want to keep those predicate whole values change from initial value
        # predicates whole value never change from the initial are always true or always false
        init = boolFvs[0][idx]
        keep = False
        for fv in boolFvs:
            if is_true(simplify(fv[idx] != init)):
                keep = True
        
        if not keep:
            idxsToRemove.append(idx)
            #remainingCondTruePredicates.append(boolFeats[idx])
            #idxsValuesToKeep.append(idx)
        else:
            remainingCondTruePredicates += (boolFeats[idx],)
        #elif is_true(init):
        #    universallyTrue.append(boolFeats[idx])
        
        #elif is_false(init):
        #    universallyTrue.append( boolFeats[idx])
    #remove values from feature vectors
    idxsToRemove.reverse()
    
    condTrueFvs = []
    for vecIdx in range(0, len(boolFvs)):
        changedBoolFv = None
        if len(idxsToRemove) > 0:
            changedBoolFv  = FeatureVector.copyFeatureVector(boolFvs[vecIdx])
            for idx in idxsToRemove:
                changedBoolFv.values = changedBoolFv.values[0:idx] + changedBoolFv.values[idx+1:]
                changedBoolFv.valuesZ3 = changedBoolFv.valuesZ3[0:idx] + changedBoolFv.valuesZ3[idx+1:]
                changedBoolFv.ID = boolFvs[vecIdx].ID
            condTrueFvs.append(changedBoolFv)
            
        else:
            condTrueFvs.append(boolFvs[vecIdx])

    return (remainingCondTruePredicates,condTrueFvs,universallyTrue)

#boolFeatures will not contain negation        
def replaceInfixToAtoms(postcondition, atoms, boolFeatures):
    
    
    for idx in range(len(boolFeatures) - 1 , -1,-1): # this code relies on the fact that Not(boolExpr) occurs later in list than boolExpr
    #for idx in range(0 ,len(boolFeatures)):
        if idx == 23:
            print("debugger")
        strZ3FeatureToReplace = boolFeatures[idx].varName
        strZ3FeatureNegated = str(Not(boolFeatures[idx].varZ3))      
        #both positive and negative case  
        if strZ3FeatureNegated in postcondition and strZ3FeatureToReplace in postcondition:
            postcondition = postcondition.replace(strZ3FeatureNegated, "(not "+atoms[idx]+")")
            postcondition = postcondition.replace(strZ3FeatureToReplace, atoms[idx])
        
        #only positive case
        elif strZ3FeatureToReplace in postcondition:
            postcondition = postcondition.replace(strZ3FeatureToReplace, atoms[idx])  
            #assert(False)#"error same cond mapt to Not(x==1) and x==1"
        #only negative case
        elif strZ3FeatureNegated in postcondition and strZ3FeatureToReplace not in postcondition:
            postcondition = postcondition.replace(strZ3FeatureNegated, "(not "+atoms[idx]+")")
        

    return postcondition
    
def replace(postcondtion, atoms, boolFeatures):
    import re
    toMatch = "cond\d+"
    matches = list(set(re.findall(toMatch, postcondtion)))
    matches = sorted(matches)
    output = postcondtion
    for idx in range (len(matches) - 1, -1, -1):
        index = getIndex(matches[idx])

        output = output.replace(matches[idx], boolFeatures[index].varName)
    # This code may not generalize if applied to exression of comparisons applied to integer boolean features to integer boolean features
    output = output.replace("Not", "!")
    return output
    

def getIndex(string):
    ret = ''.join([i for i in string if i.isdigit()])
    return int(ret)

def generateAtomPredicates(num):
    atoms=[]
    for i in range(0,num):
        atoms.append( "cond"+str(i) )
    return atoms

def synthesizeUniqueFeatures(intBaseFeat, boolBaseFeat, baseFeatureValues, exclude, synthesizer):
        syntFeats : Tuple[PrecisFeature] = synthesizer.synthesizeFeatures(intBaseFeat, boolBaseFeat, baseFeatureValues)  
        # if boolBaseFeat empty, no derived bool features will be generated -> consider refactor
        genFeats : Tuple[PrecisFeature] = synthesizer.GenerateDerivedFeatures(intBaseFeat, boolBaseFeat) 
        derivFeats : Tuple[PrecisFeature] = Featurizer.mergeSynthesizedAndGeneratedFeatures(syntFeats, genFeats)
        uniqueDerivFeats = tuple([f for f in derivFeats if f not in exclude])
        return uniqueDerivFeats

if __name__ == '__main__':
    # region logger
    
    # endregion
    outputFileType = os.path.abspath('../typesOM.txt')
    subjects = []
    
    #region Stack
    sln = os.path.abspath('../../ContractsSubjects/Stack/Stack.sln')
    projectName = 'StackTest'
    testDebugFolder = '../../ContractsSubjects/Stack/StackTest/bin/Debug/'
    testDll = testDebugFolder + 'StackTest.dll'
    testFileName = 'StackContractTest.cs'
    testNamepace = 'Stack.Test'
    testClass = 'StackContractTest'
    stackPUTs = ['PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract', 'PUT_PopContract','PUT_PushContract']
    

    #stackPUTs = ['PUT_ContainsContract']
    pStack = Problem(sln, projectName, testDebugFolder, testDll,
                testFileName, testNamepace, testClass,stackPUTs)

    #p.puts = ['PUT_PushContract']
    #p.puts = ['PUT_PeekContract']
    #runSynthTightDT(p, p.puts, p.projectName , outputFileType)
    #sys.exit(0)
    

#######################################################################################################################
    #subjects.append(p)
    #endregion of Stack

    #region HashSet
    sln = os.path.abspath('../../ContractsSubjects/HashSet/HashSet.sln')
    projectName = 'HashSetTest'
    testDebugFolder = '../../ContractsSubjects/HashSet/HashSetTest/bin/Debug/'
    testDll = testDebugFolder + 'HashSetTest.dll'
    testFileName = 'HashSetContractTest.cs'
    testNamepace = 'HashSet.Test'
    testClass = 'HashSetContractTest'
    hashsetPUTs = ['PUT_AddContract', 'PUT_RemoveContract','PUT_ContainsContract','PUT_CountContract']

    

    pHashSet = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass, hashsetPUTs)
    
    #subjects.append(p1)
    #endregion of HashSet

    #region Dictionary
    sln = os.path.abspath('../../ContractsSubjects/Dictionary/Dictionary.sln')
    projectName = 'DictionaryTest'
    testDebugFolder = '../../ContractsSubjects/Dictionary/DictionaryTest/bin/Debug/'
    testDll = testDebugFolder + 'DictionaryTest.dll'
    testFileName = 'DictionaryContractTest.cs'
    testNamepace = 'Dictionary.Test'
    testClass = 'DictionaryContractTest'
    dictionaryPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_GetContract', 'PUT_SetContract',
                      'PUT_ContainsKeyContract', 'PUT_ContainsValueContract', 'PUT_CountContract']
    
    pDictionary = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,dictionaryPUTs)
    
    #subjects.append(p2)
    #endregion of Dictionary

    #region Queue
    sln = os.path.abspath('../../ContractsSubjects/Queue/Queue.sln')
    projectName = 'QueueTest'
    testDebugFolder = '../../ContractsSubjects/Queue/QueueTest/bin/Debug/'
    testDll = testDebugFolder + 'QueueTest.dll'
    testFileName = 'QueueContractTest.cs'
    testNamepace = 'Queue.Test'
    testClass = 'QueueContractTest'
    queuePUTs = ['PUT_EnqueueContract', 'PUT_DequeueContract',
                 'PUT_PeekContract', 'PUT_ContainsContract','PUT_CountContract']
    
    pQueue = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,queuePUTs )
    
    #subjects.append(p3)
    
    #endregion Queue

    #region ArrayList
    sln = os.path.abspath('../../ContractsSubjects/ArrayList/ArrayList.sln')
    projectName = 'ArrayListTest'
    testDebugFolder = '../../ContractsSubjects/ArrayList/ArrayListTest/bin/Debug/'
    testDll = testDebugFolder + 'ArrayListTest.dll'
    testFileName = 'ArrayListContractTest.cs'
    testNamepace = 'ArrayList.Test'
    testClass = 'ArrayListContractTest'
    arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract',
                     'PUT_GetContract', 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']
    
    pArrayList = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,arrayListPUTs)
    
    #subjects.append(p4)
    #p4.puts = ['PUT_CountContract']
    ##### Developing HERE
    #runSynthTightDT(p4, p4.puts, p4.projectName , outputFileType)
    #sys.exit(0)

    #endregion of ArrayList

    #region UndirectedGraph
    sln = os.path.abspath('../../ContractsSubjects/UndirectedGraph3/UndirectedGraph.sln')
    projectName = 'UndirectedGraphTest'
    testDebugFolder = '../../ContractsSubjects/UndirectedGraph3/UndirectedGraphTest/bin/Debug/'
    testDll = testDebugFolder + 'UndirectedGraphTest.dll'
    testFileName = 'UndirectedGraphContractTest.cs'
    testNamepace = 'UndirectedGraph.Test'
    testClass = 'UndirectedGraphContractTest'
    ugraphPUTs = ['PUT_AddVertexContract', 'PUT_RemoveVertexContract','PUT_ClearAdjacentEdgesContract','PUT_ContainsEdgeContract', 'PUT_RemoveVertexContract',
                    'PUT_ContainsEdgeIntContract', 'PUT_AdjacentEdgeContract', 'PUT_IsVerticesEmptyContract', 'PUT_VertexCountContract', 'PUT_ContainsVertexContract',
                    'PUT_AddEdgeContract', 'PUT_RemoveEdgeContract', 'PUT_IsEdgesEmptyContract', 'PUT_EdgeCountContract', 'PUT_AdjacentDegreeContract',
                    'PUT_IsAdjacentEdgesEmptyContract']

    #ugraphPUTs = ['PUT_AddEdgeContract', 'PUT_RemoveEdgeContract', 'PUT_IsEdgesEmptyContract', 'PUT_EdgeCountContract', 'PUT_AdjacentDegreeContract']
    #ugraphPUTs = ['PUT_IsAdjacentEdgesEmptyContract']

    pUndirectedGraph = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,ugraphPUTs)
    
    #subjects.append(p5)
    #endregion of UndirectedGraph

    #C:\Users\astor\Research\LearningContracts\ContractsSubjects\BinaryHeap3\BinaryHeapTest\BinaryHeapContractTest.cs
    #region BinaryHeap
    sln = os.path.abspath('../../ContractsSubjects/BinaryHeap3/BinaryHeap.sln')
    projectName = 'BinaryHeapTest'
    testDebugFolder = '../../ContractsSubjects/BinaryHeap3/BinaryHeapTest/bin/Debug/'
    testDll = testDebugFolder + 'BinaryHeapTest.dll'
    testFileName = 'BinaryHeapContractTest.cs'
    testNamepace = 'BinaryHeap.Test'
    testClass = 'BinaryHeapContractTest'
    heapPUTs = ['PUT_MinimumContract', 'PUT_MinimumUpdateContract', 'PUT_UpdateContract', 'PUT_RemoveAtContract',
                     'PUT_RemoveMinimumContract', 'PUT_AddContract', 'PUT_IndexOfContract']
    
    
    pBinaryHeap = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,heapPUTs)
    
    #endregion BinaryHeap
    #subjects.append(p6)

    #region NetBigInteger
    sln = os.path.abspath('../../ContractsSubjects/NetBigInteger/NetBigInteger.sln')
    projectName = 'NetBigIntegerTest'
    testDebugFolder = '../../ContractsSubjects/NetBigInteger/NetBigIntegerTest/bin/Debug/'
    testDll = testDebugFolder + 'NetBigIntegerTest.dll'
    testFileName = 'NetBigIntegerContractTest.cs'
    testNamepace = 'NetBigInteger.Test'
    testClass = 'NetBigIntegerContractTest'
    heapPUTs = ['PUT_AbsContract', 'PUT_AddContract', 'PUT_AndContract', 'PUT_BitLengthGetContract', 'PUT_CompareToContract', 'PUT_CompareTo01Contract', 'PUT_ConstructorContract', 'PUT_Constructor01Contract', 'PUT_Constructor02Contract', 'PUT_Constructor03Contract', 'PUT_Constructor04Contract', 'PUT_Constructor05Contract', 'PUT_DivideContract', 'PUT_DivideAndRemainderContract', 'PUT_Equals01Contract', 'PUT_GcdContract', 'PUT_GetHashCode01Contract', 'PUT_GetLowestSetBitContract', 'PUT_IntValueGetContract', 'PUT_MaxContract', 'PUT_MinContract', 'PUT_ModContract', 'PUT_ModInverseContract', 'PUT_ModPowContract', 'PUT_ModulusContract', 'PUT_MultiplyContract', 'PUT_NegateContract', 'PUT_RemainderContract', 'PUT_ShiftLeftContract', 'PUT_ShiftRightContract', 'PUT_SignValueGetContract', 'PUT_SubtractContract', 'PUT_TestBitContract', 'PUT_ToByteArrayContract', 'PUT_ToByteArrayUnsignedContract', 'PUT_ToString01Contract', 'PUT_ToString02Contract', 'PUT_ValueOfContract'
    ]
    
    pNetBigInteger = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,heapPUTs)

    #subjects.append(p7)
    #endregion NetBigInteger

    angello = True
    if angello:
        #pDictionary.puts =['PUT_SetContract']
        #subjects.append(pDictionary)
        subjects.append(pArrayList)
        #, 'PUT_ContainsContract'
        #pHashSet.puts = ['PUT_ContainsContract']
        #pHashSet.puts = ['PUT_CountContract']
        #subjects.append(pArrayList)
        #pQueue.puts =['PUT_CountContract']
        #subjects.append(pQueue)
    else:
        pass

    logger1 = logging.getLogger("Results")
    logger1.setLevel(logging.INFO)
    
    evalutating = True 
    if evalutating:
        #stackPUTs = ['PUT_PushContract']
        #for prob in subjects:
        for idx in range(0, (len(subjects)) ):
            prob = subjects[idx]
            
            #resultFileName = "results"
            #resultFileName = "results_"+str(prob.projectName)
            resultFileName = "regression_results_"+str(prob.projectName)
            fh1 = logging.FileHandler(resultFileName)
            formatter1 = logging.Formatter('%(message)s')
            fh1.setFormatter(formatter1)
            logger1.addHandler(fh1)
            
            print(prob.projectName)
            print(prob.puts)
            # run all cases up to k
            #runLearnPost(prob, prob.puts, prob.projectName , outputFileType, 2)
            
            runSynthTightDT(prob, prob.puts, prob.projectName , outputFileType)
            #runLearnPostTest(prob, prob.puts, prob.projectName , outputFileType, 2)
            
            #Run one test and one case
            #break
            #learnPostUpToK(prob,prob.puts[0],outputFileType,1)
            #Testing: just call learnUpToK
            #sys.exit(0)
        # End ArrayList

    else:
        #unit tests
        #(p,['PUT_PopContract']), """ remove before this """,
        #unitTests = [(p5,['PUT_AddVertexContract'] ), """ remove before this """,(p,['PUT_PushContract']), (p, ['PUT_ContainsContract']), (p1, ['PUT_AddContract']), (p3,['PUT_DequeueContract']),(p2,['PUT_ContainsValueContract']) ]
        #unitTests = [(p2,['PUT_AddContract'])]
        #unitTests = [(p,['PUT_PushContract'])]
        #unitTests = [(p1,['PUT_ContainsContract'])]
        #unitTests = [(p,['PUT_PushContract'])]
        #unitTests = [(p7, ['PUT_AbsContract'])]
        unitTests = [(pStack, ['PUT_CountContract'])] 
        for t in unitTests:
            resultFileName = "regression_results_2"+str(t[0].projectName)
            fh1 = logging.FileHandler(resultFileName)
            formatter1 = logging.Formatter('%(message)s')
            fh1.setFormatter(formatter1)
            logger1.addHandler(fh1)
            prob = t[0] # t[0] -> problem
            prob.puts = t[1] # t[1] -> list of PUTs
            print(prob.projectName)
            print(prob.puts)
            # run all cases up to k
            #runLearnPost(prob, prob.puts, prob.projectName , outputFileType, 1)
            runLearnPostTest(prob, prob.puts, prob.projectName , outputFileType, 2)
            break