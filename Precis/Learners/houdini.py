from z3 import *
import itertools
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
import logging

logger = logging.getLogger("Runner.Houdini")
logger1 = logging.getLogger("Results.Houdini")
class Houdini:
    
    useBounds = False

    
    def learn(self,features,featureVectors,call):
        assert(len(featureVectors) > 0)
        
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        #workList = list(features)
        #oldCount = len(workList)
        for idx in range(0, len(features)):
            #fv is of type feature vector
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if str(fv[idx]) == "False":
                   workList[idx]  = False
                   break 
        conjuncts = []
        
        for idx in range(0, len(features)):
            if workList[idx]:
                conjuncts.append(features[idx].varZ3)
        
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            assert(False) #remove this assertion the first time it is tested
            return PrecisFormula(BoolVal(True))
        
        phi = ""
        houdini = None
        phi = And(conjuncts)
        houdini = PrecisFormula(phi)
        return houdini
    
    def learn2(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info("houdini Called with 0 feature vectors")
            return (PrecisFormula(BoolVal(True)),[])
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        #workList = list(features)
        #oldCount = len(workList)
        for idx in range(0, len(features)):
            
            #fv is of type feature vector
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if str(fv[idx]) == "False":
                   workList[idx]  = False
                   break 
        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                conjuncts.append(features[idx].varZ3)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[])
        
        phi = ""
        houdini = None
        phi = And(conjuncts)
        houdini = PrecisFormula(phi)
        return (houdini,indexes)