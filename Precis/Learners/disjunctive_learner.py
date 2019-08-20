from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini
from os import sys
from typing import List
import math
import numpy
import logging


logger = logging.getLogger("Runner.DisjunctiveLearner")

class DisjunctiveLearner:

    # entropy measure is used by default for choosing Predicates to split data on
    # for now we choose, largest entropy
    useEntropy = True
    featureSynthesizer = None
    
    def __init__(self, featureSynthesizer, entropy=True):
        self.useEntropy = entropy
        self.featureSynthesizer = featureSynthesizer 

    def learn2(self,k, features, featureVectors, call):
        houdini = Houdini()
        if k == 0:
            (formula, indices) = houdini.learn2(features, featureVectors, call)
            return (formula, indices)
        else:
            reaminingEntriesFv =list()
            (allTrueFormula, indicesAllwaysTrue) = houdini.learn2(features, featureVectors, call)
            remainingFeatures: List[PrecisFeature] = self.removeFeatureFromFeaturelist(features,indicesAllwaysTrue)
            reaminingEntriesFv = self.removeFeatureEntryInFeatureVectors(featureVectors, indicesAllwaysTrue)
            
            #FIXME: allow chooseFeature to be overridden in derived classes
            (f,idx, fposFv,fnegFv) = self.chooseFeature(remainingFeatures, reaminingEntriesFv, call)
            
            conditionallyTrueFeatures = self.removeFeatureFromFeaturelist(remainingFeatures,[idx])
            
            #posFv = list()
            #negFv = list()
            posFv = self.removeFeatureEntryInFeatureVectors(fposFv, [idx])
            negFv = self.removeFeatureEntryInFeatureVectors(fnegFv, [idx])
            #for fv in fposFv:
            #    fposFeatureVector = FeatureVector([], [], str(fv.testLabel))
            #    fposFeatureVector.values = fv.values[0:idx] + fv.values[idx+1:] 
            #    fposFeatureVector.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]
            #    posFv.append(fposFeatureVector)
            #for fv in fnegFv:
            #    fnegFeatureVector = FeatureVector([], [], str(fv.testLabel))
            #    fnegFeatureVector.values = fv.values[0:idx] + fv.values[idx+1:]                
            #    fnegFeatureVector.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]
            #    negFv.append(fnegFeatureVector)

            
            #print( [ len(fv)  for fv in fposFv] )
            #print( [ len(fv)  for fv in fnegFv] )
            (posPost,posIndices) = self.learn2(k-1,conditionallyTrueFeatures,posFv, "pos")
            (negPost, negIndices) = self.learn2(k-1,conditionallyTrueFeatures,negFv, "neg")
            print("for call "+call +" at k == "+str(k))
            print("choosen for split for :", f)
            #print("positive: ",posPost.formula )
            print("positive: ",posPost.toInfix())
            #print("negative: ",negPost.formula)
            print("negative: ",negPost.toInfix())
            print()
            print("result of conjunction")
            #Todo: missing conjunction with split predicate
            #disjunction = Or(And(posPost.formulaZ3, f.varZ3), negPost.formulaZ3)
            disjunction  = And(allTrueFormula.formulaZ3, Or(And(posPost.formulaZ3, f.varZ3),negPost.formulaZ3))
            #stringDisjunc = "(or(and New_s1ContainsX (not (= Old_s1Count New_s1Count)) (not (= New_s1Count Old_Top)) (not (= New_s1Count New_Top)) (not ( = New_s1Count  Old_x)) (not (= New_s1Count New_x)) (= Old_Top New_Top) (= Old_Top Old_x) (= New_Top Old_x) (= New_Top New_x) (= Old_x  New_x ))(and New_s1ContainsX (not (= Old_s1Count New_s1Count)) (not(= Old_s1Count Old_Top)) (not (= New_s1Count Old_Top)) (not (= New_s1Count New_Top)) (not ( = New_s1Count  Old_x)) (not (= New_s1Count New_x)) (not (= Old_Top New_Top)) (not(= Old_Top Old_x)) (not (= Old_Top New_x)) (= New_Top Old_x) (= New_Top New_x) (= Old_x  New_x )))"
            #result = self.precisSimplify(stringDisjunc,['Old_s1Count', 'New_s1Count', 'Old_Top', 'New_Top', 'Old_x', 'New_x'],["Old_s1ContainsX", "New_s1ContainsX"])
            
            #for conjuct in result:
            #    print(type(conjuct))
            #    print(conjuct)
            #nextFeatureVector.values =  
            #nextFeatureVector.valuesZ3 = self.valuesZ3 + derivedValuesZ3
            return PrecisFormula(disjunction), posIndices + negIndices

    def learn(self,k, features, featureVectors, call):
        houdini = Houdini()
        
        if k == 0:
            return houdini.learn(features, featureVectors, call)
        else:
            (f,idx, fposFv,fnegFv) = self.chooseFeature(features, featureVectors, call)
            
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
                fv.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:] # this assignments affect the variable featureVectors
            
            for fv in fnegFv:
                fv.values = fv.values[0:idx] + fv.values[idx+1:]
                fv.valuesZ3 = fv.valuesZ3[0:idx] + fv.valuesZ3[idx+1:]
            #print( [ len(fv)  for fv in fposFv] )
            #print( [ len(fv)  for fv in fnegFv] )
            posPost = self.learn(k-1,newFeatures,fposFv, "pos")
            negPost = self.learn(k-1,newFeatures,fnegFv, "neg")
            print("for call "+call +" at k == "+str(k))
            print("choosen for split for :", f)
            #print("positive: ",posPost.formula )
            print("positive: ",posPost.toInfix())
            #print("negative: ",negPost.formula)
            print("negative: ",negPost.toInfix())
            print()
            print("result of conjunction")
            #Todo: missing conjunction with split predicate
            disjunction = Or(And(posPost.formulaZ3, f.varZ3), negPost.formulaZ3)
            #disjunction = 
            #stringDisjunc = "(or(and New_s1ContainsX (not (= Old_s1Count New_s1Count)) (not (= New_s1Count Old_Top)) (not (= New_s1Count New_Top)) (not ( = New_s1Count  Old_x)) (not (= New_s1Count New_x)) (= Old_Top New_Top) (= Old_Top Old_x) (= New_Top Old_x) (= New_Top New_x) (= Old_x  New_x ))(and New_s1ContainsX (not (= Old_s1Count New_s1Count)) (not(= Old_s1Count Old_Top)) (not (= New_s1Count Old_Top)) (not (= New_s1Count New_Top)) (not ( = New_s1Count  Old_x)) (not (= New_s1Count New_x)) (not (= Old_Top New_Top)) (not(= Old_Top Old_x)) (not (= Old_Top New_x)) (= New_Top Old_x) (= New_Top New_x) (= Old_x  New_x )))"
            #result = self.precisSimplify(stringDisjunc,['Old_s1Count', 'New_s1Count', 'Old_Top', 'New_Top', 'Old_x', 'New_x'],["Old_s1ContainsX", "New_s1ContainsX"])
            
            #for conjuct in result:
            #    print(type(conjuct))
            #    print(conjuct)
            #nextFeatureVector.values =  
            #nextFeatureVector.valuesZ3 = self.valuesZ3 + derivedValuesZ3
            return PrecisFormula(disjunction)

            
    #return feature along with index
    def chooseFeature(self, features, featureVectors, call):
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
            
        #experimental score metric incorporating length of formula- consider prioritizing  old_vars over new vars
        sortedScores = sorted(allScores, key=lambda x: x['score'] + (x['score']/len(x['predicate'].varZ3.children())) )
        #sortedScores = sorted(allScores, key=lambda x: x['score'] )
        
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


    #fix this
    def removeFeatureEntryInFeatureVectors(self,featureVectors, indices):
        newFeatureVectors = list()
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for fv in featureVectors:
                newFeatureVector = FeatureVector([], [], str(fv.testLabel))
                newFeatureVector.values = tuple(fv.values)
                newFeatureVector.valuesZ3 = tuple(fv.valuesZ3)
                for idx in reversed(indices):
                        newFeatureVector.values = newFeatureVector.values[0:idx] + newFeatureVector.values[idx+1:]
                        newFeatureVector.valuesZ3 = newFeatureVector.valuesZ3[0:idx] + newFeatureVector.valuesZ3[idx+1:]
                newFeatureVectors.append(newFeatureVector)
        else:
            assert(False)
        return newFeatureVectors

    
    def removeFeatureFromFeaturelist(self,features,indices):
        
        newFeatures = list(features)
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            
            for idx in reversed(indices):
                newFeatures = newFeatures[0:idx]+ newFeatures[idx+1:]
            
        else:
            assert(False)
        
        return newFeatures

if __name__ == '__main__':

    #PrecisFeature: def __init__(self, isDerived, varName, varType=None, isNew=None, varZ3=None):

    feature1 = PrecisFeature(False, "New_Containsx", "BOOL", "New_Containsx".startswith("New_"), None)