from z3 import *
import itertools
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
import logging

logger = logging.getLogger("Runner.Houdini")

class Houdini:
    
    useBounds = False

    def concatenateFeatureVectors(self, baseFeatureVectors, derivedValuesZ3Tuples):
        featureVectors = []
        for i in range(len(baseFeatureVectors)):
            featureVectors.append(baseFeatureVectors[i] + derivedValuesZ3Tuples[i])
        return featureVectors
    
    def getBoolFeatures(self, precisFeatureList):
        boolFeatures = []
        boolFeatureIndices = []
        for idx in range(len(precisFeatureList)):
            if is_bool(precisFeatureList[idx].varZ3):
                boolFeatures.append(precisFeatureList[idx])
                boolFeatureIndices.append(idx)
        return boolFeatures, boolFeatureIndices
    
    def getBoolFeatureVectors(self, featureVectorList, boolFeatureIndices):
        boolFeatureVectors = []
        for featureVector in featureVectorList:
            boolFeatureVector = FeatureVector([], [], str(featureVector.testLabel))
            boolFeatureVector.valuesZ3 = tuple(featureVector.valuesZ3[i] for i in boolFeatureIndices)
            boolFeatureVector.values = tuple(featureVector.values[i] for i in boolFeatureIndices)
            boolFeatureVectors.append(boolFeatureVector)
        return boolFeatureVectors

    # Inputs:
    #   baseFeatures: list of PrecisFeature containing features provided by user in Parameterized Unit Test(i.e., PUTs)
    #   deriveFeatures: list of PrecisFeature containing feature created from the user provided base features
    #   (i.e., return values of observer methods, and/or parameters of methods and return variables of the method)
    #   baseFeatureVectors: 
    # This funtion extends each FeatureVector object in baseFeatureVector(.i.e., list of FeatureObjects)
    # to contain entries of valuation of derivedFeatures(this shall be boolean features only)
    def generateDerivedFeatureVectors(self, derivedFeatures, baseFeatures, baseFeatureVectors):
        
        #print(derivedFeatures)
        #print(baseFeatureVectors)
        #print ("here")
        #print(baseFeatures)
        pairs = list()
        # consider
        allDerivedFeatureVectors = list()
        for f in baseFeatureVectors:
            #print("feature vec: " +str(f))
            pairs = Houdini.generateFeatureValueMapping(baseFeatures,f)
            #print(pairs)
            #print(type(pairs))
            derivedFeatureVector = ()
            for df in derivedFeatures:
                deriveFeatVec = substitute(df.varZ3 , pairs)
                deriveFeatVecValue = simplify(deriveFeatVec)
                derivedFeatureVector += (deriveFeatVecValue,)
            # Assert: # of derived feature values(i.e. length of derived feature vector(tuple)) should be the same as
            # Assert: # of derived features (.i.e length of list of derived features)
            assert(len(derivedFeatureVector) == len(derivedFeatures))
            
            allDerivedFeatureVectors.append(derivedFeatureVector)
        
        #print(allDerivedFeatureVectors)
        return allDerivedFeatureVectors

    @staticmethod
    def generateFeatureValueMapping(baseFeatures, featureVector):
        pairs = list()
        # consider removing check for perfomances in cases where the number of feature vectors gets large.
        # number of base features should be the same as the number of entries in feature vector(values of said features)
        assert(len(featureVector) == len(baseFeatures))
        for i in  range(len(baseFeatures)):
            #print("type of featVec", type(featureVector[i]))
            pair = (baseFeatures[i].varZ3 , featureVector[i])
            pairs.append(pair)
        return pairs


    def learn(self,features,featureVectors):
        assert(len(featureVectors) > 0)
        #check datapoint are boolean
        assert(len(featureVectors) or all ( all( v == "true" or v == "false" for v in dp) for dp in featureVectors))
    
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
        