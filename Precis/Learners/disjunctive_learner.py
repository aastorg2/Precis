from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini

from os import sys

class DisjunctiveLearner:

    # entropy measure is used by default for choosing Predicates to split data on
    # for now we choose, largest entropy
    useEntropy = True

    def learn(self,k, features, featureVectors):
        houdini = Houdini()
        if k == 0:
            return houdini.learn(features, featureVectors)
        else:
            self.chooseFeature(features, featureVectors)

    #return feature along with index
    def chooseFeature(self, features, featureVectors):
        fvFPos = list()
        fvFNeg = list()
        for idx in range(0, len(features)):
            (fvFPos, fvFNeg) = self.splitSamples(features[idx], idx, featureVectors)


            sys.exit(0)

    # f is for feature of PrecisFeature type
    def splitSamples(self, f, idx, featureVectors):
        posF = list()
        negF = list()
        # add assertion check that every entry  in feature vector, fv, in list, featureVectors, is of type z3.z3.BoolRef
        # is_true(True) returns False; True is a python boolean expression. is_true(BoolVal(True)) returns True 
        print(len(featureVectors))
        for fv in featureVectors:
            if is_true(fv[idx]):
                posF.append(fv)
            else:
                negF.append(fv)
        #assert(len(featureVectors) == len(posF)+ len(negF))
        return (posF, negF)
        
            