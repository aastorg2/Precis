from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini

from os import sys
import math
import numpy
import logging

logger = logging.getLogger("Runner.DisjunctiveLearner")
class DisjunctiveLearner:

    # entropy measure is used by default for choosing Predicates to split data on
    # for now we choose, largest entropy
    useEntropy = True

    def learn(self,k, features, featureVectors):
        houdini = Houdini()
        if k == 0:
            return houdini.learn(features, featureVectors)
        else:
            (f,idx, fposFv,fnegFv) = self.chooseFeature(features, featureVectors)
            
            #region
            print("feature:", f)
            print("index: ", idx)
            print()
            print(fposFv)
            print()
            print( [ fv[idx]  for fv in fposFv] )
            print()
            print(fnegFv)
            print()
            print( [ fv[idx]  for fv in fnegFv] )
            #endregion
            #region checking removal of feature

            # print("before length: ",len(features))
            # check = [ nf for nf in features if nf.varZ3 == f.varZ3] 
            # print(check)
            # features = features[0:idx]+ features[idx+1:]
            # check = [ nf for nf in features if nf.varZ3 == f.varZ3] 
            # print(check)
            # print("length: ", len(features))
            #endregion 
            
            #region checking removal of value of feature at index in feature vector
            #print("before removal")
            # fvLens = [ len(fv) for fv in featureVectors ]
            # print(fvLens)
            
            # valueAtIdx  = [ fv[idx] for fv in featureVectors ]
            # print("feature value before removing:")
            # print(valueAtIdx)

            #for fv in featureVectors:
            #    fv.values = fv.values[0:idx] + fv.values[idx+1:]
            #    fv.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]
            # nextfvLens = [ len(fv.values) for fv in featureVectors ]
            # print("after removal")
            # print(nextfvLens)
            
            # valueAtIdx  = [ fv[idx] for fv in featureVectors ]
            # print("feature value after removing:")
            # print(valueAtIdx)
            #nextFeatureVector = FeatureVector([], [], str(.testLabel))
            #endregion
            newFeatures = features[0:idx]+ features[idx+1:]

            for fv in fposFv:
                fv.values = fv.values[0:idx] + fv.values[idx+1:]
                fv.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]
            
            for fv in fnegFv:
                fv.values = fv.values[0:idx] + fv.values[idx+1:]
                fv.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]

            #print( [ len(fv)  for fv in fposFv] )
            #print( [ len(fv)  for fv in fnegFv] )
            #posPost = learn(k-1,newFeatures,fposFv)
            #negPost = learn(k-1,newFeatures,fnegFv)

            #print("positive: ",posPost.toInfix())
            #print("negative: ",negPost.toInfix())

            
            #nextFeatureVector.values =  
            #nextFeatureVector.valuesZ3 = self.valuesZ3 + derivedValuesZ3


            
    #return feature along with index
    def chooseFeature(self, features, featureVectors):
        # TODO: figure is removing always false predicates will lead to optimizations
        fvPos = list()
        fvNeg = list()
        
        allScores = []
        for idx in range(0, len(features)):
            (fvPos, fvNeg) = self.splitSamples(features[idx], idx, featureVectors) 
            #skip always false predicates
            #if len(fvPos) == 0 and len(fvNeg)> 0:
            #    continue
            posLabel = ['+'] * len(fvPos)
            negLabel = ['-'] * len(fvNeg)
            score = self.entropy(posLabel+negLabel)
            allScores.append({'predicate': features[idx],'idx': idx, 'score': score , 'posData':fvPos, 'negData': fvNeg} )
            
        
        sortedScores = sorted(allScores, key=lambda x: x['score'])
        #for entry in sortedScores:
        #    logger.info("predicate: "+ str(entry['predicate']))
        #    logger.info("predicate: "+ str(entry['score']))
        #return highest entropy
        return (sortedScores[-1]['predicate'], sortedScores[-1]['idx'], sortedScores[-1]['posData'], sortedScores[-1]['negData']) 

    # f is for feature of PrecisFeature type
    def splitSamples(self, f, idx, featureVectors):
        posF = list()
        negF = list()
        # add assertion check that every entry  in feature vector, fv, in list, featureVectors, is of type z3.z3.BoolRef
        # is_true(True) returns False; True is a python boolean expression. is_true(BoolVal(True)) returns True 
        #print(len(featureVectors))
        for fv in featureVectors:
            if is_true(fv[idx]):
                posF.append(fv)
            else:
                negF.append(fv)
        #assert(len(featureVectors) == len(posF)+ len(negF))
        return (posF, negF)


    # labels is a list of all class labels 
    def entropy(self, labels, base = None):
        valueLabel, occurrencesLabel = numpy.unique(labels, return_counts=True)
        currentTotalSample = occurrencesLabel.sum()
        probability_value_attribute = numpy.true_divide(occurrencesLabel, currentTotalSample )
        base = math.e if base is None else base
        #debug code
        denominator = numpy.log(base)
        rightNumerator = numpy.log(probability_value_attribute)
        numerator = probability_value_attribute * rightNumerator
        fraction = (numerator / numpy.log(base)) # why divide by numpy.log(base) -> numpy.log(e)==1
        #end debug code
        return - (probability_value_attribute * numpy.log(probability_value_attribute) / numpy.log(base)).sum()
        # Note: I believe this implementation is missing an additional multiplication
        #return - ((probability_value_attribute/initialTotalSample)* probability_value_attribute * numpy.log(probability_value_attribute) / numpy.log(base)).sum()

if __name__ == '__main__':

    #PrecisFeature: def __init__(self, isDerived, varName, varType=None, isNew=None, varZ3=None):

    feature1 = PrecisFeature(False, "New_Containsx", "BOOL", "New_Containsx".startswith("New_"), None)