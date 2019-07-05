from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class FeatureSynthesis:

    #def __init__(self):
    def GenerateDerivedFeatures(self,baseFeatures):
        intFeatures = [f for f in baseFeatures if str(f.varZ3.sort())=="Int"]
        self.CreateEqualities(intFeatures)

    def CreateEqualities(self, intFeatures):
        print(intFeatures)
        #create copy constructor for PrecisFeature
        if len(intFeatures) >= 2:
            allCombinations = itertools.combinations(intFeatures,2)
            for (feat1,feat2) in allCombinations:
                print (feat1, feat2)
                notEqualExpr = feat1.varZ3 != feat2.varZ3
                print(notEqualExpr)
                print(type(notEqualExpr))

        """
        namesDataFile = list()
        if len(intVars) >= 2:
            all_combination = itertools.combinations(intVars, 2)
            for (var1, var2) in all_combination:
                namesExpr = "(= " + var1 + " " + var2 + ")"
                dataExpr = "(" + var1 + " == " + var2 + ")"
                namesDataFile.append((namesExpr, dataExpr))

                namesExpr = "(not (= "  + var1 + " " + var2 + "))"
                dataExpr = "(not ("  + var1 + " == " + var2 + "))"
                namesDataFile.append((namesExpr, dataExpr))
                
        return namesDataFile
        """