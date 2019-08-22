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


    def createCompleteFeatureVectors(self):
        self.derivedFVs = self.generateDerivedFeatureVectors(self.derivedFeatures, self.baseFeatures, self.baseFVs)
        self.completeFVs = self.aggregateFeatureVectors(self.baseFVs, self.derivedFVs)
        (self.boolFeatures,self.boolFeaturesIndices) = self.getBoolFeatures(self.features)
        self.boolFVs = self.getBoolFeatureVectors(self.completeFVs,self.boolFeaturesIndices)

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
    
    def getBoolFeatures(self, precisFeatureList):
        boolFeatures = ()
        boolFeatureIndices = []
        for idx in range(0,len(precisFeatureList)):
            if is_bool(precisFeatureList[idx].varZ3):
                boolFeatures += (precisFeatureList[idx],)
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