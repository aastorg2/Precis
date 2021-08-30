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




def synthesizeKTightTree(feats, featureVectors, k, currentTree:str):
    output_tree = Nd
    solver1 = SygusDisjunctive(
                            feats,
                            featureVectors,
                            rounds,
                            k=k,
                            cdt=currentTree)
            startKExecTime = time.time()
            output_tree = solver1.run_sygus()
            # properties of output_tree are that 
            # 1.  Every fv in fvWithSynth evaluates to true on output_tree 
            # 2.  output_tree => currentBestTreeAtK
            #assert(checkWeakening(houdini, fvWithSynth, featWithSynt, previousContract , output_tree)), "This has certainly found bug"
            kExecTime = time.time() - startKExecTime
            timePerK.append( (k, kExecTime) )
            totalLearningTime = totalLearningTime + kExecTime
