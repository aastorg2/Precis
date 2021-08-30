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

import logging


logger1 = logging.getLogger("Results.propertyChecks")

def checkIncludesAllSamplesZ3(previousContract:PrecisFormula, baseFvs, baseFeats):
    if previousContract.formulaZ3 == BoolVal(False):
        return False

    for fv in baseFvs:
        #print("feature vec: " +str(fv))
        pairs = Featurizer.generateFeatureValueMapping(baseFeats,fv)
        # print(pairs)
        # print(type(pairs))
        subsResult = substitute(previousContract.formulaZ3, pairs)
        valuation = simplify(subsResult)
        assert(valuation == BoolVal(True) or valuation == BoolVal(False)), "formula should simplify to True or false"
        if valuation ==  BoolVal(False):
            return False
        
    return True




def checkIncludesAllSamples(houdini, tree, fvWithSynth, featWithSynt,  baseFvs, baseFeats):
    if tree == None:
        logger1.info("tree is none at this k")
        print("tree is none at this k")
        return True

    if tree.data == None:
        return False
    
    lastestTreeSmtStr, strongerTree, synthFeatures, timePredSynth = houdini.houdiniSynthesis(tree, featWithSynt, fvWithSynth, "root")
    for fv in baseFvs:
        #print("feature vec: " +str(fv))
        pairs = Featurizer.generateFeatureValueMapping(baseFeats,fv)
        # print(pairs)
        # print(type(pairs))
        subsResult = substitute(strongerTree.formulaZ3, pairs)
        valuation = simplify(subsResult)
        assert(valuation == BoolVal(True) or valuation == BoolVal(False)), "formula should simplify to True or false"
        if valuation ==  BoolVal(False):
            return False
        
    return True
        


def checkStrength(houdini, featureVecs, features, lastestTree:Nd, cdt:PrecisFormula):
    
    if lastestTree == None:
        return True

    lastestTreeSmtStr, strongerTree, synthFeatures, timePredSynth = houdini.houdiniSynthesis(lastestTree, features, featureVecs, "root")
        
    
    implication = Implies(strongerTree.formulaZ3, cdt.formulaZ3) # a => b
    otherWayImplication = Implies(cdt.formulaZ3, strongerTree.formulaZ3) # b => a simplify ~b || a neg: True && a 
    solver = Solver()
    solver2 = Solver()
    #check (not (postK0 => postK1)) is unsat
    solver.add(Not(otherWayImplication))
    solver2.add(Not(implication))
    #x strongerTree, y true
    
    check = solver2.check()
    
    if check == sat:
        return False
    elif check == unsat: 
        otherCheck = solver.check()
        if otherCheck == sat:
            return True
        return False
    else:
        raise ValueError

def checkWeakening(houdini, featureVecs, features, prevRoundContract:PrecisFormula, currentStrongContract:Nd) :
    if currentStrongContract == None:
        return True

    lastestTreeSmtStr, strongerTree, synthFeatures, timePredSynth = houdini.houdiniSynthesis(currentStrongContract, features, featureVecs, "root")    

    otherWayImplication = Implies(strongerTree.formulaZ3, prevRoundContract.formulaZ3)
    implication = Implies(prevRoundContract.formulaZ3, strongerTree.formulaZ3)

    solver = Solver()
    solver2 = Solver()
    #check (not (postK0 => postK1)) is unsat
    solver.add(Not(otherWayImplication))
    solver2.add(Not(implication))
    #x strongerTree, y true
    
    check = solver2.check()
    
    if check == sat:
        return False
    elif check == unsat: 
        otherCheck = solver.check()
        if otherCheck == sat:
            return True
        return False
    elif check == unknown:
        raise ValueError
    else:
        raise ValueError