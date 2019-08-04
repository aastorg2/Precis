from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class FeatureSynthesis:

    #def __init__(self):
    def GenerateDerivedFeatures(self,baseFeatures):
        intFeatures = [f for f in baseFeatures if str(f.varZ3.sort())=="Int"]
        boolFeatures = [f for f in baseFeatures if str(f.varZ3.sort())=="Bool"]
        sygusResult = "(= New_s1Count (- Old_New1Count  1))"
        negationBaseBoolFeatures =[]
        #minus = precisFeature.oldcount - IntVal(1)
        #equal = precisFeature.New  
        #sygusPrecisFeature = PrecisFeature(sygusResult, )
        assert(len(intFeatures) > 0)
        #assert(len(boolFeatures) > 0)
        equalityFeatures = self.CreateEqualities(intFeatures)
        
        if len(boolFeatures) > 0: # there exist any base bool observer methods
            negationBaseBoolFeatures = self.createNegationBool(boolFeatures)
        
        return negationBaseBoolFeatures+equalityFeatures
        #return equalityFeatures
        #Todo: call to sygus solvers can be placed here.
    def createNegationBool(self, boolFeatures):
        negBoolFeatures = list()
        for bf in boolFeatures:
            negBoolExpr = Not(bf.varZ3)
            negBoolDerive = PrecisFeature(True, str(negBoolExpr), str(negBoolExpr.sort()), None, negBoolExpr)
            negBoolFeatures.append(negBoolDerive)
        return negBoolFeatures

    # this method assumes it called with integer features
    def CreateEqualities(self, intFeatures):
        equalitiesFeatures = list()        
        
        if len(intFeatures) <= 1:
            return intFeatures # throw new error
        
        allCombinations = itertools.combinations(intFeatures,2)
        
        for (feat1,feat2) in allCombinations:
            #print (feat1, feat2)
            notEqualExpr = feat1.varZ3 != feat2.varZ3
            equalExpr = feat1.varZ3 == feat2.varZ3
            #print(notEqualExpr)
            #print(notEqualExpr.sort())
            #print(type(notEqualExpr))
            notEqualDerived = PrecisFeature(True, str(notEqualExpr), str(notEqualExpr.sort()), None, notEqualExpr)
            equalDerived = PrecisFeature(True, str(equalExpr), str(equalExpr.sort()), None, equalExpr)
            equalitiesFeatures.append(notEqualDerived)
            equalitiesFeatures.append(equalDerived)
        return equalitiesFeatures
    