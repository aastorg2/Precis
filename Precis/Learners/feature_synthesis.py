from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class FeatureSynthesis:

    #def __init__(self):
    def GenerateDerivedFeatures(self,baseFeatures):
        intFeatures = [f for f in baseFeatures if str(f.varZ3.sort())=="Int"]
        sygusResult = "(= New_s1Count (- Old_New1Count  1))"

        #minus = precisFeature.oldcount - IntVal(1)
        #equal = precisFeature.New  
        #sygusPrecisFeature = PrecisFeature(sygusResult, )
        return self.CreateEqualities(intFeatures)
        #Todo: call to sygus solvers can be placed here.

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
            notEqualDerived = PrecisFeature(True, str(notEqualExpr), None, None, notEqualExpr)
            equalDerived = PrecisFeature(True, str(equalExpr), None, None, equalExpr)
            equalitiesFeatures.append(notEqualDerived)
            equalitiesFeatures.append(equalDerived)
        return equalitiesFeatures
    