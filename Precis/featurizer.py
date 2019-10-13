from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini
from os import sys
from typing import List
import numpy
import logging


class Featurizer:
    baseFeatures = None
    baseFVs = None
    derivedFeatures = None
    #this should be tuples of base plus derived features
    features = None
    boolFeatures = None
    boolFeaturesIndices = None

    
    
    derivedFVs = None
    #tuple of complete(base + derived) feature vectors
    completeFVs = None
    boolFVs = None
   
    
    # Todo: either derivedFeatures and basefeatures is redundant or features is
    def __init__(self, derivedFeatures, baseFeatures, baseFeatureVectors, features):
        self.baseFVs = baseFeatureVectors
        self.baseFeatures = baseFeatures
        self.derivedFeatures = derivedFeatures
        self.features = features

    @staticmethod
    def getIntAndBoolFeatures(baseFeatures):
        intFeats = ()
        boolFeats = ()
        for f in baseFeatures:
            if str(f.varZ3.sort()).upper() == 'INT':
                intFeats = intFeats + (f,)
            elif str(f.varZ3.sort()).upper() == 'BOOL':
                boolFeats = boolFeats + (f,)
        return intFeats, boolFeats

    def getBaseFeaturesAndIndices(self,features):
        indices = ()
        base = ()
        for idx in range(0,len(features)):
            if not features[idx].isDerived:
                indices += (idx,)
                base += (features[idx],)
        return (base,indices)
    
    def getBaseFVs(self, FeatureVectors, indices):
        newBaseFeatureVectors = list()
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for fv in FeatureVectors:
                newBaseFV = FeatureVector([], [], str(fv.testLabel))
                newBaseFV.valuesZ3 = tuple(fv[i] for i in indices) 
                newBaseFV.values = tuple(str(fv[i]) for i in indices)
                newBaseFeatureVectors.append(newBaseFV)
        else:
            assert(False)
        return newBaseFeatureVectors

    def generateRemainingFeatureVectors(self, derivedFeatures, baseFeatures, baseFVs):
        derivedFVs = self.generateDerivedFeatureVectors(derivedFeatures, baseFeatures, baseFVs)
        completeFVs = self.aggregateFeatureVectors(baseFVs, derivedFVs)
        return completeFVs

    
    @staticmethod
    def getBoolAndIntFeatureVectors(intFeats, boolFeats, baseFeatureVectors):
        intFVs =[]
        boolFVs = []
        boolOnlyFV = None
        intOnlyFV = None
        for bf in baseFeatureVectors:
            boolVal = ()
            intVal = ()
            for fVal in bf:
                #print(fVal)
                if is_bool(fVal):
                    boolVal += (str(fVal),)
                elif is_int(fVal):
                    intVal +=(str(fVal),)
            intOnlyFV = FeatureVector(intFeats, intVal, str(bf.testLabel))
            #check for empty boolVal tuple when there are 0 boolean base features
            boolOnlyFV = FeatureVector(boolFeats, boolVal, str(bf.testLabel))
            #print(boolOnlyFV)
            #print(bf)
            intFVs.append(intOnlyFV)
            boolFVs.append(boolOnlyFV)
        return (intFVs,boolFVs)

    # Inputs:
    #   baseFeatures: list of PrecisFeature containing features provided by user in Parameterized Unit Test(i.e., PUTs)
    #   deriveFeatures: list of PrecisFeature containing feature created from the user provided base features
    #   (i.e., return values of observer methods, and/or parameters of methods and return variables of the method)
    #   baseFeatureVectors: 
    # This funtion extends each FeatureVector object in baseFeatureVector(.i.e., list of FeatureObjects)
    # to contain entries of valuation of derivedFeatures(this shall be boolean features only)
    @staticmethod
    def generateDerivedFeatureVectors( derivedFeatures, baseFeatures, baseFeatureVectors):
        
        #print(derivedFeatures)
        #print(baseFeatureVectors)
        #print ("here")
        #print(baseFeatures)
        pairs = list()
        #consider
        allDerivedFeatureVectors = list()
        for f in baseFeatureVectors:
            #print("feature vec: " +str(f))
            pairs = Featurizer.generateFeatureValueMapping(baseFeatures,f)
            #print(pairs)
            #print(type(pairs))
            derivedTupleValuesZ3 = ()
            for df in derivedFeatures:
                deriveFeatVec = substitute(df.varZ3 , pairs)
                deriveFeatVecValue = simplify(deriveFeatVec)
                derivedTupleValuesZ3 += (deriveFeatVecValue,)

            # Assert: # of derived feature values(i.e. length of derived feature vector(tuple)) should be the same as
            # Assert: # of derived features (.i.e length of list of derived features)
            assert(len(derivedTupleValuesZ3) == len(derivedFeatures))
            derivedFeatureVector = FeatureVector([], [], str(f.testLabel))
            derivedFeatureVector.valuesZ3 = derivedTupleValuesZ3
            derivedFeatureVector.values = tuple(str(i) for i in derivedTupleValuesZ3)
            allDerivedFeatureVectors.append(derivedFeatureVector)
        
        #print(allDerivedFeatureVectors)
        return allDerivedFeatureVectors

    # assumes ith element in baseFeatureVectors corresponds to ith element in  derivedValuesZ3Tuples
    def aggregateFeatureVectors(self, baseFeatureVectors, derivedFeatureVector):
        featureVectors = ()
        for i in range(0,len(baseFeatureVectors)):
            concatenatedFv = baseFeatureVectors[i] + derivedFeatureVector[i]
            featureVectors += (concatenatedFv,)
        return featureVectors
    
    
    
    # def getBoolFeatureVectors(self, featureVectorList, boolFeatureIndices):
    #     boolFeatureVectors = []
    #     for featureVector in featureVectorList:
    #         boolFeatureVector = FeatureVector([], [], str(featureVector.testLabel))
    #         boolFeatureVector.valuesZ3 = tuple(featureVector.valuesZ3[i] for i in boolFeatureIndices)
    #         boolFeatureVector.values = tuple(featureVector.values[i] for i in boolFeatureIndices)
    #         boolFeatureVectors.append(boolFeatureVector)
    #     return boolFeatureVectors

    @staticmethod
    #checks for duplicates before merging
    def mergeSynthesizedAndGeneratedFeatures(synthFeat, genFeat):
        mergedFeatures = tuple(synthFeat)
        if len(synthFeat) == 0:
            return genFeat
        else:
            for f in genFeat:
                if not (f in synthFeat): # this is a brittle check a != b and b != a returns false
                    mergedFeatures += (f,)
            return mergedFeatures

    @staticmethod
    #checks for duplicates before merging
    def mergeFeatureVectors(baseBoolFvs, derivBoolFvs):
        #Add case if any one of the inputs is empty
        mergedFvs = []
        for i in range(0,len(baseBoolFvs)):
            merged = baseBoolFvs[i]+ derivBoolFvs[i]
            mergedFvs.append(merged)
        return mergedFvs 
            
    

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