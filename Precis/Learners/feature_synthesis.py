from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class FeatureSynthesis:

    #def __init__(self):
    def GenerateDerivedFeatures(self,baseFeatures):
        intFeatures = [f for f in baseFeatures if str(f.varZ3.sort())=="Int"]
        return self.CreateEqualities(intFeatures)

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
            notEqualDerived = PrecisFeature.create(True,notEqualExpr ,str(notEqualExpr.sort()))
            equalDerived = PrecisFeature.create(True,equalExpr ,str(equalExpr.sort()))
            equalitiesFeatures.append(notEqualDerived)
            equalitiesFeatures.append(equalDerived)
        return equalitiesFeatures
    