from z3 import *
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from Learners.houdini import Houdini

class DisjunctiveLearner:


    def learn(self,k, features, featureVectors):
        houdini = Houdini()
        if k == 0:
            return houdini.learn(features, featureVectors)
        else:
            pass

    #return feature along with index
    def chooseFeature(self, type):
        if type =="ENTROPY":
            pass
        
            