from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini
from featurizer import Featurizer
from os import sys
from typing import List, Tuple, Type
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

    def learn3(self, k, intBaseFeat, boolBaseFeat, baseFeatureVectors, excluded, call):
        
        syntFeats : Tuple[PrecisFeature] = self.featureSynthesizer.synthesizeFeatures(intBaseFeat, boolBaseFeat, baseFeatureVectors)
        genFeats : Tuple[PrecisFeature] = self.featureSynthesizer.GenerateDerivedFeatures(intBaseFeat, boolBaseFeat)
        derivFeats : Tuple[PrecisFeature] = Featurizer.mergeSynthesizedAndGeneratedFeatures(syntFeats, genFeats)
        
        derivFeatVectors: List[FeatureVector] = Featurizer.generateDerivedFeatureVectors(derivFeats, intBaseFeat+boolBaseFeat,baseFeatureVectors )
        #assert(len(baseFeatureVectors) == len(derivFeatVectors))
        boolBaseFeatVectors = Featurizer.getBoolFeatureVectors(boolBaseFeat, baseFeatureVectors)
        boolFvs = Featurizer.mergebaseBoolAndDerivedBoolFVs(boolBaseFeatVectors,derivFeatVectors)
        
        
        houdini = Houdini()
        (formula, indicesAllwaysTrue) = houdini.learn2(boolBaseFeat + derivFeats , boolFvs, call)
        print(indicesAllwaysTrue)
        if k == 0:
            return (formula,indicesAllwaysTrue)
        else:
            (remainingBaseBoolFeat, remainingDerivBoolFeat)  = self.removeFeatureFromFeaturelist(boolBaseFeat,derivFeats, indicesAllwaysTrue)
            (reaminingEntriesBaseBoolFv, reaminingEntriesDerivBoolFv) = self.removeFeatureEntryInFeatureVectors(boolBaseFeatVectors,derivFeatVectors, indicesAllwaysTrue)
            
            #(f,idx, fposFv,fnegFv) = self.chooseFeature(remainingBoolFeatures, reaminingEntriesBoolFv, call)
            
            return (formula,indicesAllwaysTrue)
            
        #houdini.learn2(boolBaseFeat + derivFeats, Bool(baseFeatureVectors)+derivFeatsVectors )
    #baseFeatures is a tuple
    def learn2(self,k, baseFeatures, baseFeatureVectors, call):
        self.featureSynthesizer.updateBaseFeatures(baseFeatures)
        
        derivedFeatures  = Featurizer.mergeSynthesizedAndGeneratedFeatures( \
            self.featureSynthesizer.synthesizeFeatures(), self.featureSynthesizer.GenerateDerivedFeatures())
        
        features: Tuple[PrecisFeature] = baseFeatures + derivedFeatures
        featureVectors = Featurizer.generateRemainingFeatureVectors(derivedFeatures, baseFeatures, baseFeatureVectors)
        
        houdini = Houdini()
        
        if k == 0:
            (formula, indices) = houdini.learn2(baseFeatures, baseFeatureVectors, call)
            return (formula, indices)
        else:

            
            (allTrueFormula, indicesAllwaysTrue) = houdini.learn2(baseFeatures, baseFeatureVectors, call)
            #subject stack push: newContains is removed so cannot evaluate derived preds  
            remainingBoolFeatures: Tuple[PrecisFeature] = self.removeFeatureFromFeaturelist(baseFeatures,indicesAllwaysTrue)
            reaminingEntriesBoolFv: List[FeatureVector] = self.removeFeatureEntryInFeatureVectors(baseFeatureVectors, indicesAllwaysTrue)
            
            #FIXME: allow chooseFeature to be overridden in derived classes
            (f,idx, fposFv,fnegFv) = self.chooseFeature(remainingBoolFeatures, reaminingEntriesBoolFv, call)
            #if len(fposFv) == 0 or len(fnegFv)==0:
            #    return (PrecisFormula(BoolVal(False)),[])
            conditionallyTrueFeatures = self.removeFeatureFromFeaturelist(remainingBoolFeatures,[idx])
            posFv = self.removeFeatureEntryInFeatureVectors(fposFv, [idx])
            negFv = self.removeFeatureEntryInFeatureVectors(fnegFv, [idx])
            
            # (baseFeatures, indices) = featurizer.getBaseFeaturesAndIndices(conditionallyTrueFeatures)
            
            # basePosFv = featurizer.getBaseFVs(posFv, indices)
            # self.featureSynthesizer.updateBaseFeatures(baseFeatures)
            # self.featureSynthesizer.updateBaseFeatureVector(basePosFv)
            # posDerivedFeatures =  self.featureSynthesizer.synthesizeFeatures() + \
            #     featurizer.derivedFeatures
            # posFeatures = baseFeatures + posDerivedFeatures
            # #posFeatures =  conditionallyTrueFeatures + posDerivedFeatures
            # posFeaturizer = Featurizer(posDerivedFeatures, baseFeatures, basePosFv, posFeatures)
            # posFeaturizer.createCompleteFeatureVectors()
            (posPost,posIndices) = self.learn2(k-1, conditionallyTrueFeatures, posFv, "left")  #recursive call
            
            # baseNegFv = featurizer.getBaseFVs(negFv, indices)
            # self.featureSynthesizer.updateBaseFeatures(baseFeatures)
            # self.featureSynthesizer.updateBaseFeatureVector(baseNegFv)
            # negDerivedFeatures =  self.featureSynthesizer.synthesizeFeatures() + \
            #     featurizer.derivedFeatures
            # #negFeatures = baseFeatures + negDerivedFeatures
            # negFeatures = baseFeatures + negDerivedFeatures
            # negFeaturizer = Featurizer(negDerivedFeatures, baseFeatures,baseNegFv, negFeatures)
            # negFeaturizer.createCompleteFeatureVectors()
            (negPost, negIndices) = self.learn2(k-1,conditionallyTrueFeatures, negFv, "right") #recursive call
            
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
            disjunction  = And(allTrueFormula.formulaZ3, Or(And(posPost.formulaZ3, f.varZ3), And(negPost.formulaZ3,Not(f.varZ3) )))
            #disjunction  = And(allTrueFormula.formulaZ3, Or(And(posPost.formulaZ3, f.varZ3), negPost.formulaZ3 ))
            
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
            #print("positive: ",posPost.toInfix())
            #print("negative: ",negPost.formula)
            #print("negative: ",negPost.toInfix())
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
            if is_int(features[idx].varZ3):
                continue
            (fvPos, fvNeg) = self.splitSamples(features[idx], idx, featureVectors) 
            #skip always false predicates
            #if len(fvPos) == 0 and len(fvNeg)> 0:
            #    continue
            posLabel = ['+'] * len(fvPos)
            negLabel = ['-'] * len(fvNeg)
            score = self.entropy(posLabel+negLabel)
            multiplier = 0
            if len(features[idx].varZ3.children()) == 0:
                multiplier = 1
            else:
                multiplier = len(features[idx].varZ3.children()) + 1.0
            rank = score + (score / multiplier )
            allScores.append({'predicate': features[idx],'idx': idx, 'score': score ,'rank':rank , 'posData':fvPos, 'negData': fvNeg} )
            
        #experimental score metric incorporating length of formula- consider prioritizing  old_vars over new vars
        #sortedScores = sorted(allScores, key=lambda x: x['score'] + (x['score'] /  len([1]) if len(x['predicate'].varZ3.children())== 0 else len(x['predicate'].varZ3.children()) )  )
        #sortedScores = sorted(allScores, key=lambda x: x['score'] + (x['score'] / len(x['predicate'].varZ3.children()) ) )
        sortedScores = sorted(allScores, key=lambda x: x['rank'])
        #sortedScores = sorted(allScores, key=lambda x: x['rank'] )
        
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
    def removeFeatureEntryInFeatureVectors(self,baseFvs, derivFvs, indices):
        newBaseFvs = list()
        newDerivFvs = list()
        if len(baseFvs) == 0:
            assert(False)
        # len(baseFvs) == len(derivFvs) should hold when this function is called
        #numOfFvs = len(baseFvs)
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for idxFV in range(0, len(baseFvs)):
                derivIdx =-2
                FeatureVector.copyFeatureVector(derivFvs[idxFV])
                newDerivFv = FeatureVector.copyFeatureVector(derivFvs[idxFV])
                newBaseFv = FeatureVector.copyFeatureVector(baseFvs[idxFV])
                
                for idx in reversed(indices):
                    if idx >= len(baseFvs[idxFV]):
                        #compute new index for removing entry in derivFV
                        derivIdx = idx - len(baseFvs[idxFV]) 
                        newDerivFv.values = newDerivFv.values[0:derivIdx] + newDerivFv.values[derivIdx+1:]
                        newDerivFv.valuesZ3 = newDerivFv.valuesZ3[0:derivIdx] + newDerivFv.valuesZ3[derivIdx+1:]
                    else:
                        newBaseFv.values = newBaseFv.values[0:idx] + newBaseFv.values[idx+1:]
                        newBaseFv.valuesZ3 = newBaseFv.valuesZ3[0:idx] + newBaseFv.valuesZ3[idx+1:]
                        
                newBaseFvs.append(newBaseFv)
                newDerivFvs.append(newDerivFv)
        else:
            assert(False)
        return (newBaseFvs, newDerivFvs)

    
    def removeFeatureFromFeaturelist(self,baseFeatures,derivFeatures,indices):
        
        newBaseFeatures = tuple(baseFeatures)
        newDerivFeatures = tuple(derivFeatures)
        if all(indices[i] <= indices[i+1] for i in range(len(indices)-1)):
            for idx in reversed(indices):
                if idx >= len(baseFeatures):
                    idx = idx - len(baseFeatures)
                    newDerivFeatures = newDerivFeatures[0:idx]+ newDerivFeatures[idx+1:]
                else:
                    newBaseFeatures = newBaseFeatures[0:idx]+ newBaseFeatures[idx+1:]
            
        else:
            assert(False)
        
        return (newBaseFeatures, newDerivFeatures)

if __name__ == '__main__':

    #PrecisFeature: def __init__(self, isDerived, varName, varType=None, isNew=None, varZ3=None):

    feature1 = PrecisFeature(False, "New_Containsx", "BOOL", "New_Containsx".startswith("New_"), None)