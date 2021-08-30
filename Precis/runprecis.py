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
from Learners.sygus2 import Nd, SygusDisjunctive
from Learners.houdini import Houdini
from featurizer import Featurizer
import shutil
from typing import List, Tuple, Type
import logging
import evaluation
import pickle
import re
from importlib import reload
import propertyChecks
#import precis

#import numpy as np
import cProfile

print("In precis.py: \n" + str(sys.path))
#learning function 1 --- based decision tree learning not synthesis
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


def readSavedFeatureVectors(baseFeatures):
    unserializedFvs =[]
    with open("allBaseFeatureVec.txt", "r") as fr:
        textFvs = fr.readlines()
    
    for fv in textFvs:
        fvsRead = ()
        res = re.match(r"\((-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+), (True|False), (True|False), TL=(True|False), L=(True|False)\)",fv) 
        for i in range(1, 11):
            val = res.group(i)
            fvsRead += (val,)
        tl = res.group(11)  
        readFv = FeatureVector(baseFeatures ,fvsRead,tl)
        unserializedFvs.append(readFv)
    return unserializedFvs


def SynthTightDT2(p, PUTName, outputFile, destinationOfTests, maxK):
    sygusExecutable = "./Learners/EnumerativeSolver/bin/starexec_run_Default"
    tempLocation = "../tempLocation"
    sygusFileName = "postcondition.sl"
    #assumes MSBuils.exe in path
    inst = Instrumenter("MSBuild.exe", "../Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")
    p.ExtractObservers(PUTName, outputFile, "precis") # writes observers and their return types to ../typesOM.txt
    
    # returns list of base features
    baseFeatures: Tuple[PrecisFeature] = p.ReadObserversFromFile(outputFile)
    allBaseFeatureVectors = []

    synthesizer = FeatureSynthesis(sygusExecutable, tempLocation, sygusFileName)
    currentStringTree = "false"
    inst.instrumentPostString(p, currentStringTree, PUTName)
    
    rounds = 1
    totalPexTime = 0.0
    totalLearningTime = 0.0
    predSyntTimeTotal = 0.0
    candidatePost = None
    simplifiedPost =""
    print(p, PUTName, outputFile, destinationOfTests)

    intBaseFeatures, boolBaseFeatures = Featurizer.getIntAndBoolFeatures(baseFeatures)
    templateFeats = synthesizer.GenerateDerivedFeatures(intBaseFeatures, boolBaseFeatures) 
    
    uniqueSynthFeats = ()
    synthFeatReturn = ()
    candidatePostSimp =None
    contractsPerRound = []
    previousContract = PrecisFormula(BoolVal(False))
    previousTree = Nd()
    feats = []
    preciFeat = []
    textFvs=[]
    while True:
        msg4 = f"Round: {rounds} ====\n"
        print(msg4)
        logger1.info(msg4)

        print("============================================================================= starting round: " + str(rounds))
        #For this kind of learner, consider optimizing by generating fixed templates once. Only call sygus per round.
        pex = Pex()
        startTimePex = time.time()
        baseFeatureVectors: List[FeatureVector] = pex.RunTeacher(p, PUTName, baseFeatures)
        pexTime = time.time() - startTimePex
        totalPexTime = totalPexTime + pexTime
        print("Pex Finished")
        #copy tests
        evaluation.copyTestFilesToEvaluationDir(pex.testsLocation, destinationOfTests, rounds)

        if all(baseFeatureVectors[i].testLabel for i in range(0, len(baseFeatureVectors))):
            #In the first round, 
            print("found it")
            simplifiedPost = PrecisFormula(candidatePostSimp.precisSimplify()).toInfix()
            return candidatePostSimp, candidatePostSimp.toInfix(), simplifiedPost, rounds, totalPexTime, totalLearningTime, len(allBaseFeatureVectors), predSyntTimeTotal, synthFeatReturn
        
        if rounds == 20: # debugging purposely only because we should never trigger this
            print("did not find it - Max Rounds")
            break
        #region inspectingReturn
        allBaseFeatureVectors.extend(baseFeatureVectors)

        #allBaseFeatureVectors += readSavedFeatureVectors(baseFeatures)
       
        (intBaseFeatVectors, boolBaseFeatVectors) = Featurizer.getBoolAndIntFeatureVectors(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors)
        synthFeats, predSyntTime = synthesizer.synthesizeFeatures(intBaseFeatures, boolBaseFeatures, allBaseFeatureVectors) # TODO: this function does not require Bool 
        predSyntTimeTotal += predSyntTime
        
        uniqueSynthFeats = tuple([f for f in synthFeats if f not in templateFeats])
        for f in uniqueSynthFeats:
             templateFeats = templateFeats + (f,)
             synthFeatReturn = synthFeatReturn + (f,)
             print(f"Adding Unique synthesized feature: {f.varName}" )
             logger1.info(f"Adding Unique synthesized feature: {f.varName}" )
        
        derivFeats = templateFeats
        derivFeatVecs = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeatures+boolBaseFeatures,allBaseFeatureVectors)
        # will have to change order: boolBaseFeatures at the end, while deriv at the beginning.
        boolFeats =  derivFeats + boolBaseFeatures
        
        boolFeatVecs = Featurizer.mergeFeatureVectors(derivFeatVecs, boolBaseFeatVectors) 


        k = 1
        config = False
        #currentBestTreeAtK = condPostSmtAtom
        currentBestTreeAtK = 'true' # type string
        lastTighthestTree = None # type Nd or Node
        stringTree = ""
        stringTreeReplaced = ""
        timePerK = []
        houdini = Houdini(intBaseFeatures, boolBaseFeatures, intBaseFeatVectors, boolBaseFeatVectors, derivFeats, synthesizer)
        # recommended to remove predicates that are universillay true or universally false. 
        conditionalFeats,conditionalFvs,alwaysTrue = removeUniversallyTrueFalse(boolFeats, boolFeatVecs) 
        
        withSynth = False
        newlySynthesizedFeatures = ()
        allKTrees = []
        currentTighterPost = PrecisFormula(BoolVal(True))
        
        while True and k <= maxK:
            featWithSynt = conditionalFeats
            fvWithSynth = conditionalFvs
            
            assert(k <= maxK), f"Reached max k: {maxK} for round: {rounds} in problem: {PUTName}"

            print("=================================================== looking for tighter k-tight tree="+str(k))
            if len(newlySynthesizedFeatures) > 0: # if we synthesized a new feature, then we need to update feature vectors
                withSynth = True
                featWithSynt = conditionalFeats + newlySynthesizedFeatures
                synthFvs = Featurizer.generateDerivedFeatureVectors(newlySynthesizedFeatures,intBaseFeatures+boolBaseFeatures, allBaseFeatureVectors)
                fvWithSynth = Featurizer.mergeFeatureVectors(conditionalFvs, synthFvs)
            

            solver1 = SygusDisjunctive(
                            conditionalFeats if not withSynth else featWithSynt,
                            conditionalFvs if not withSynth else fvWithSynth,
                            rounds,
                            k=k,
                            cdt=currentBestTreeAtK)
            startKExecTime = time.time()
            output_tree = solver1.run_sygus()
            # properties of output_tree are that 
            # 1.  Every fv in fvWithSynth evaluates to true on output_tree 
            # 2.  output_tree => currentBestTreeAtK
            #assert(checkWeakening(houdini, fvWithSynth, featWithSynt, previousContract , output_tree)), "This has certainly found bug"
            kExecTime = time.time() - startKExecTime
            assert(propertyChecks.checkIncludesAllSamples(houdini, output_tree, fvWithSynth, featWithSynt, allBaseFeatureVectors, baseFeatures )), "Maybe found another bug"
            assert(propertyChecks.checkStrength(houdini, fvWithSynth, featWithSynt, output_tree, currentTighterPost)), "Maybe found bug"
            assert(not propertyChecks.checkIncludesAllSamplesZ3(previousContract, allBaseFeatureVectors, baseFeatures )), "Maybe bug with Pex or how we are collecting samples"
            timePerK.append( (k, kExecTime) )
            totalLearningTime = totalLearningTime + kExecTime
            

            if output_tree != None: # phase1: exhaust trees at k
                #[output_tree, ]
                allKTrees.append(output_tree)
                print("++++++++++++++ latest "+ str(k)+"-tree root: "+ str(output_tree))
                logger1.info("++++++++++++++ latest "+ str(k)+"-tree root: "+ str(output_tree))

                # houdiniSynthesis will call houdini at leaves and replace boolean variables with predicates; so returned tree has predicates; 
                # will also call predicate synthesis at leaves
                currentBestTreeAtK, currentTighterPost, synthFeatures, timePredSynth = houdini.houdiniSynthesis(output_tree, featWithSynt, fvWithSynth, "root")
                predSyntTimeTotal += timePredSynth
                if len(synthFeatures)> 0:
                    newlySynthesizedFeatures = addIfNotThereAlready(newlySynthesizedFeatures, synthFeatures)
                    synthFeatReturn = addIfNotThereAlready(synthFeatReturn, synthFeatures)
                    #updating global state
                    houdini.derivBoolFeats = addIfNotThereAlready(houdini.derivBoolFeats , newlySynthesizedFeatures)
                    templateFeats = addIfNotThereAlready(templateFeats,newlySynthesizedFeatures)
                    
                lastTighthestTree = output_tree 

            
            elif lastTighthestTree != None: #False when tighthestTree == None
                #phase 2: check if there is a better tree before moving on to k+1. Note however when currentBestTree is None, then it must mean 
                #there was no tree of depth k so will skip checking at k+1
                # at this point, currentBestTreeAtK has the best tree of depth k. So now, we check if there exist a better tree of depth k+1
                #copy2StrBoolFvs = list(strBoolFvs)
                #copyboolFvs = list (boolFvs)
                
                print("(sygus format before k+1 check) Tight "+str(k)+"-tree:\n")
                print(""+currentBestTreeAtK)
                logger1.info("(sygus format before k+1 check) Tight "+str(k)+"-tree:\n")
                logger1.info(""+currentBestTreeAtK)
                #print("z3 simplified:\n"+PrecisFormula(currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy2StrBoolFvs, copyboolFvs, s1, "root").precisSimplify()).toInfix()+"\n") # destroys copy2StrBoolFvs
                
                print("checking if there exist a tree at k+1 depth that is tigher?: k+1=" + str(k + 1) )
                logger1.info("checking if there exist a tree at k+1 depth that is tigher? k+1="+ str(k + 1))
                solver2 = SygusDisjunctive(
                            conditionalFeats if not withSynth else featWithSynt,
                            conditionalFvs if not withSynth else fvWithSynth,
                            rounds,
                            k=(k+1), #Angello: change to k+2 for RQ
                            cdt=currentBestTreeAtK)
                startKExecTime = time.time()
                output_tree = solver2.run_sygus()
                kExecTime = time.time() - startKExecTime
                totalLearningTime = totalLearningTime + kExecTime
                timePerK.append( (k+1, kExecTime) )
                assert(propertyChecks.checkIncludesAllSamples(houdini,output_tree,fvWithSynth, featWithSynt, allBaseFeatureVectors, baseFeatures )), "Maybe found another bug"
                assert(propertyChecks.checkStrength(houdini, fvWithSynth, featWithSynt, output_tree, currentTighterPost)), "Maybe found bug"
                
                if output_tree != None:
                    #copy3StrBoolFvs = list(strBoolFvs)
                    #copy2boolFvs = list (boolFvs)
                    print("Yes, tighter tree at k+1")
                    currentBestTreeAtK, currentTighterPost, synthFeatures, timePredSynth = houdini.houdiniSynthesis(output_tree, featWithSynt, fvWithSynth, "root")
                    predSyntTimeTotal += timePredSynth
                    if len(synthFeatures)> 0:
                        newlySynthesizedFeatures = addIfNotThereAlready(newlySynthesizedFeatures, synthFeatures)
                        synthFeatReturn = addIfNotThereAlready(synthFeatReturn, synthFeatures)
                        #updating global state 
                        houdini.derivBoolFeats = addIfNotThereAlready(houdini.derivBoolFeats , newlySynthesizedFeatures)
                        templateFeats = addIfNotThereAlready(templateFeats,newlySynthesizedFeatures)
                    
                    print("k+1-tree Stronger than k-tree :\n"+currentBestTreeAtK+"\n")
                    print("k+1-tree Stronger post precis: \n"+ PrecisFormula(currentTighterPost.precisSimplify()).toInfix())
                    logger1.info("k+1-tree Stronger than k-tree :\n"+currentBestTreeAtK+"\n")
                    logger1.info("k+1-tree Stronger post precis: \n"+ PrecisFormula(currentTighterPost.precisSimplify()).toInfix())
                    #print("z3 simplified:\n"+PrecisFormula(output_tree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copy3StrBoolFvs, copy2boolFvs, s1, "root").precisSimplify()).toInfix()+"\n")# destroys copy3StrBoolFvs
                    lastTighthestTree = output_tree #  this insurances we continue checking at next level(enter this branch) even if there are no further stronger trees in current level check done in previous if condition.                    
                    k = k + 1 #Angello: change to k+2 for RQ
                else:
                    msg7 = "there is no k+1-tree stronger than k-tree: k+1-tree= " + str(k+1)+"-tree"
                    print(msg7)
                    logger1.info(msg7)
                    previousContract = currentTighterPost
                    previousTree = lastTighthestTree
                    contractsPerRound.append(currentTighterPost)
                    break
            else:# we hit this case the very first time around the loop when formula is conjunctive or after update k = old(k)+1 and there is not tighter k-tree immediatly after update.
                msg = f"Round: {rounds} k: {k} There is not disjunctive formula"
                logger1.info(msg)
                print(msg)
                break

        
        print("round: "+str(rounds))
        for idx in range(0, len(timePerK)):
            print("k= "+str(timePerK[idx][0]) +" " +str(timePerK[idx][1]))
        
        listOfTimesPerK = [entry[1] for entry in timePerK]
        print("sygu disjunc. learning time in this round: "+ str(sum(map(float, listOfTimesPerK))) )
        print("sygu disjunc. learning time across all rounds: "+ str( totalLearningTime))
        print("Total pex time: "+str(totalPexTime))
        #endregion 
        if lastTighthestTree != None: # this is only false when there are no disjunctive concept and the tighest post is conjunctive
            #copyStrBoolFvs = list(strBoolFvs)
            #stringTree = currentBestTree.parseWithHoudini(atoms, strBoolFvs) #this call detroys strBoolFvs
            #stringTreeReplaced = replace(stringTree, atoms, boolFeatures)
            #s = Solver()
            logger1.info("found k-tightest tree for this round")
            print("found k-tightest tree for this round")
            #candidatePostcondition = currentBestTree.parseWithHoudiniWithZ3Expr(atoms, boolFeatures, copyStrBoolFvs, boolFvs, s, "root")
            
            smtCandidatePost, candidatePost, synthFeatures, timePredSynth = houdini.houdiniSynthesis(lastTighthestTree, featWithSynt, fvWithSynth, "root")
            if len(synthFeatures) !=0:
                print("something wrong Need to check &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&")
                logger1.info("something wrong Need to check &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&")
            predSyntTimeTotal += timePredSynth
            # learn6 does not return predicates that are always false
            #simplifiedPost = PrecisFormula(candidatePost.precisSimplify()).toInfix()
            print("\nlearned candidate post: disjunctive part(before simplify): \n"+ candidatePost.toInfix())
            logger1.info("\nlearned candidate post: disjunctive part(before simplify): \n"+ candidatePost.toInfix())
            candidatePostSimp = PrecisFormula(candidatePost.precisSimplify())
            print("\nlearned candidate post: disjunctive part(after simplify): \n"+ candidatePostSimp.toInfix())
            logger1.info("\nlearned candidate post: disjunctive part(after simplify): \n"+ candidatePostSimp.toInfix())
            conjunctPrecis, indices, conjuncts = houdini.learn6(boolFeats, boolFeatVecs,"root")# change this to learn6
            print("\nlearned candidate post: conjunc part(before simplify): \n"+ conjunctPrecis.toInfix())
            logger1.info("\nlearned candidate post: conjunc part(before simplify): \n"+ conjunctPrecis.toInfix())
            conjunctZ3simple = conjunctPrecis.precisSimplify()
            print("\nlearned candidate post: conjunc part(After simplify): \n"+ str(conjunctZ3simple))
            logger1.info("\nlearned candidate post: conjunc part(After simplify): \n"+ str(conjunctZ3simple))
            
            candidatePostSimp = PrecisFormula(And(conjunctZ3simple,candidatePostSimp.formulaZ3))
            print("\nlearned candidate post: conj + disj part(conj + disj simplified separately): \n"+ candidatePostSimp.toInfix())
            logger1.info("\nlearned candidate post: conj + disj part(conj + disj simplified separately): \n"+ candidatePostSimp.toInfix())
            #smtCandidatePost, candidatePost, synthFeatures = houdini.houdiniSynthesis(currentBestTree, boolFeats, boolFeatVecs, "root")

        else:
            print("no disjunctive formula")
            logger1.info("no disjunctive formula")
            conjunctPrecis, indices, conjuncts = houdini.learn5(boolFeats, boolFeatVecs,"root")
            #stringTreeReplaced = PrecisFormula(conjunctPrecis.precisSimplify()).toInfix() #Debugging
            candidatePostSimp = conjunctPrecis

        finalCandidatePost:PrecisFormula = PrecisFormula(candidatePostSimp.precisSimplify())
        strCandidatePost = finalCandidatePost.toInfix()
        print("\ncandidate post(simplied togerther): \n"+ strCandidatePost)
        logger1.info("\ncandidate post(simplied togerther): \n"+ strCandidatePost)
        inst.instrumentPostString(p, strCandidatePost, PUTName)
        rounds = rounds + 1    


def runSynthTightDT(p, putList, projectName, outputFile):
    logger1.info("Problem: "+projectName+"\n")
    for putName in putList:
        ## location to store tests
        locationOfTests = evaluation.createDirectoryForTestsWithoutCase("../evaluation2", projectName, putName)
        assert(locationOfTests != None)
        currentPost = "Timeout or error"
        learnedPostStr = "Timeout or error"
        simplifiedPostStr = "Timeout or error"
        rounds = 0
        pexTime = 0
        learnTime = 0.0
        totalSamples = 0
        predSynthTime= 0.0
        logger1.info("PUT: "+putName+"\n")
        synthFeatures = ()
        output = SynthTightDT2(p, putName, outputFile, locationOfTests , 20)
        if output:
            (currentPost, learnedPostStr, simplifiedPostStr, rounds, pexTime, learnTime, totalSamples, predSynthTime, synthFeatures) = output

        print("learnerd post:")
        print(learnedPostStr +"\n")
        print("simplified post:")
        print(simplifiedPostStr+"\n")

        logger1.info("===== Final Result for "+putName +"\n")
        logger1.info("postcondition: \n" +
                    learnedPostStr+"\nrounds: " + str(rounds) + "\n")
        logger1.info(f"simplified post:\n{simplifiedPostStr}")
        logger1.info(f"pex time: {pexTime}\n")
        logger1.info(f"learn time: {learnTime}\n")
        logger1.info(f"Samples: {totalSamples}\n")
        logger1.info(f"predicate synthesis time: {predSynthTime}\n")
        logger1.info(f"number of unique features synthesized: {len(synthFeatures)}")
        for f in synthFeatures:
            logger1.info(f"Synth Feature: {f}\n")

        #delete directory where pex initially stores tests -> we don't want old test seeding pex
        pexTestsDir = p.testDebugFolder+"/root"
        if os.path.exists(pexTestsDir):
            shutil.rmtree(pexTestsDir)
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
    

    pStack = Problem(sln, projectName, testDebugFolder, testDll,
                testFileName, testNamepace, testClass,stackPUTs)

    #p.puts = ['PUT_PushContract']
    #p.puts = ['PUT_PeekContract']
    
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
    #arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract',
    #                 'PUT_GetContract', 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']
    arrayListPUTs = ['PUT_InsertContract']
    
    pArrayList = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,arrayListPUTs)
    
    #subjects.append(p4)
    #p4.puts = ['PUT_CountContract']
    ##### Developing HERE
    #runSynthTightDT(p4, p4.puts, p4.projectName , outputFileType)
    #sys.exit(0)

    #endregion of ArrayList

    #region UndirectedGraph
    sln = os.path.abspath('../../ContractsSubjects/UndirectedGraph/UndirectedGraph.sln')
    projectName = 'UndirectedGraphTest'
    testDebugFolder = '../../ContractsSubjects/UndirectedGraph/UndirectedGraphTest/bin/Debug/'
    testDll = testDebugFolder + 'UndirectedGraphTest.dll'
    testFileName = 'UndirectedGraphContractTest.cs'
    testNamepace = 'UndirectedGraph.Test'
    testClass = 'UndirectedGraphContractTest'

    ugraphPUTs = ['PUT_VertexCountContract', 'PUT_EdgeCountContract', 'PUT_IsVerticesEmptyContract', 'PUT_IsEdgesEmptyContract',
                  'PUT_AdjacentDegreeContract', 'PUT_IsAdjacentEdgesEmptyContract', 'PUT_ClearAdjacentEdgesContract', 'PUT_AddVertexContract',
                  'PUT_AdjacentEdgeContract', 'PUT_ContainsVertexContract', 'PUT_RemoveVertexContract', 'PUT_RemoveEdgeContract',
                  'PUT_AddEdgeContract', 'PUT_ContainsEdgeContract', 'PUT_ContainsEdgeIntContract']

    #ugraphPUTs = ['PUT_AddEdgeContract', 'PUT_RemoveEdgeContract', 'PUT_IsEdgesEmptyContract', 'PUT_EdgeCountContract', 'PUT_AdjacentDegreeContract']
    #ugraphPUTs = ['PUT_IsAdjacentEdgesEmptyContract']

    pUndirectedGraph = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass,ugraphPUTs)
    
    #subjects.append(p5)
    #endregion 

    #C:\Users\astor\Research\LearningContracts\ContractsSubjects\BinaryHeap\BinaryHeapTest\BinaryHeapContractTest.cs
    #region BinaryHeap
    sln = os.path.abspath('../../ContractsSubjects/BinaryHeap/BinaryHeap.sln')
    projectName = 'BinaryHeapTest'
    testDebugFolder = '../../ContractsSubjects/BinaryHeap/BinaryHeapTest/bin/Debug/'
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
    # sln = os.path.abspath('../../ContractsSubjects/NetBigInteger/NetBigInteger.sln')
    # projectName = 'NetBigIntegerTest'
    # testDebugFolder = '../../ContractsSubjects/NetBigInteger/NetBigIntegerTest/bin/Debug/'
    # testDll = testDebugFolder + 'NetBigIntegerTest.dll'
    # testFileName = 'NetBigIntegerContractTest.cs'
    # testNamepace = 'NetBigInteger.Test'
    # testClass = 'NetBigIntegerContractTest'
    # heapPUTs = ['PUT_AbsContract', 'PUT_AddContract', 'PUT_AndContract', 'PUT_BitLengthGetContract', 'PUT_CompareToContract', 'PUT_CompareTo01Contract', 'PUT_ConstructorContract', 'PUT_Constructor01Contract', 'PUT_Constructor02Contract', 'PUT_Constructor03Contract', 'PUT_Constructor04Contract', 'PUT_Constructor05Contract', 'PUT_DivideContract', 'PUT_DivideAndRemainderContract', 'PUT_Equals01Contract', 'PUT_GcdContract', 'PUT_GetHashCode01Contract', 'PUT_GetLowestSetBitContract', 'PUT_IntValueGetContract', 'PUT_MaxContract', 'PUT_MinContract', 'PUT_ModContract', 'PUT_ModInverseContract', 'PUT_ModPowContract', 'PUT_ModulusContract', 'PUT_MultiplyContract', 'PUT_NegateContract', 'PUT_RemainderContract', 'PUT_ShiftLeftContract', 'PUT_ShiftRightContract', 'PUT_SignValueGetContract', 'PUT_SubtractContract', 'PUT_TestBitContract', 'PUT_ToByteArrayContract', 'PUT_ToByteArrayUnsignedContract', 'PUT_ToString01Contract', 'PUT_ToString02Contract', 'PUT_ValueOfContract'
    # ]
    
    #pNetBigInteger = Problem(sln, projectName, testDebugFolder, testDll,
                 #testFileName, testNamepace, testClass,heapPUTs)

    #subjects.append(p7)
    #endregion NetBigInteger

    subjects.append(pArrayList)
     

    
    
    evalutating = True 
    if evalutating:
        #stackPUTs = ['PUT_PushContract']
        #for prob in subjects:
        for idx in range(0, (len(subjects)) ):
            prob = subjects[idx]
            
            #resultFileName = "results"
            #resultFileName = "results_"+str(prob.projectName)
            resultFileName = "regression_results_"+str(prob.projectName)
            logger1 = logging.getLogger("Results")
            logger1.setLevel(logging.INFO)
            fh1 = logging.FileHandler(resultFileName)
            formatter1 = logging.Formatter('%(message)s')
            fh1.setFormatter(formatter1)
            logger1.addHandler(fh1)
            
            print(prob.projectName)
            print(prob.puts)
        
            
            runSynthTightDT(prob, prob.puts ,prob.projectName , outputFileType)
            #except:
            #    logger1.info(f"Unexpected error: {sys.exc_info()[0]}") 
            #    logger1.info(f"Unexpected error: {sys.exc_info()[1]}")
            #    logger1.info(f"Unexpected error: {sys.exc_info()[2]}")
            #runLearnPostTest(prob, prob.puts, prob.projectName , outputFileType, 2)
            
            #Run one test and one case
            #break
            #learnPostUpToK(prob,prob.puts[0],outputFileType,1)
            #Testing: just call learnUpToK
            #sys.exit(0)
        # End ArrayList

