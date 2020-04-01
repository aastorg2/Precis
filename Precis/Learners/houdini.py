from z3 import *
import itertools
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
import logging


logger1 = logging.getLogger("Results.DisjunctiveLearner.Houdini")
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
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            if "implication check" in call:
                return (PrecisFormula(BoolVal(False)),[])
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
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[])
        
        phi = ""
        houdini = None
        phi = And(conjuncts)
        houdini = PrecisFormula(phi)
        return (houdini,indexes)
    
    #return z3 expr types -> refactor: it should return precis
    def learn4(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            return (PrecisFormula(BoolVal(False)),[],[])
            
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        
        indicesToNegate = {idx: False for idx in range(0, len(features))}
        for idx in range(0, len(features)):
            #fv is of type feature vector
            initVal = featureVectors[0][idx]
            keep = True 
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if is_true(simplify(fv[idx] != initVal)):
                   workList[idx]  = False
                   keep = False
            if keep and is_false(initVal):
                indicesToNegate[idx] = True
                

        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                validFeature = features[idx]
                if indicesToNegate[idx]:
                    #sort here should be BOOL
                    z3NegatedFeature = Not(validFeature.varZ3)
                    negatedPrecisFeature = PrecisFeature(True, str(z3NegatedFeature), str(z3NegatedFeature.sort()), None, z3NegatedFeature)
                    validFeature = negatedPrecisFeature
                conjuncts.append(validFeature)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[],[])
        
        phi = ""
        houdini = None
        phi = And([c.varZ3 for c in conjuncts])
        houdini = PrecisFormula(phi)
        return (houdini,indexes,conjuncts)
    
    def learnHoudiniString(self, strFeatures, strFeatureVectors):
        workList = {key: True for key in range(0, len(strFeatures))}

        indicesToNegate = {idx: False for idx in range(0, len(strFeatures))}
        for idx in range(0, len(strFeatures)):
            initVal = strFeatureVectors[0][idx]
            keep = True
            for fv in strFeatureVectors:
                # -2 to account for the labeling
                assert(len(fv) == len(strFeatures) )
                if fv[idx] != initVal:
                   workList[idx]  = False
                   keep = False
            #no need to negate because we assume  strFeatures is just literals.
            if keep and (initVal == "false"):
                indicesToNegate[idx] = True
        
        terms = []
        indexes = []
        for idx in range(0, len(strFeatures)):
            if workList[idx]:
                if indicesToNegate[idx]:
                    terms.append("(not "+strFeatures[idx]+")")
                else:
                    terms.append(strFeatures[idx])
                indexes.append(idx)
        return (terms, indexes)
