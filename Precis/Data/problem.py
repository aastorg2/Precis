import itertools
from z3 import *

class Problem:
    def __init__(self, intVars, floatVars, boolVars, relations):
        self.intVarsZ3 = []
        self.floatVarsZ3 = []
        self.boolVarsZ3 = []

        for intVar in intVars:
            self.intVarsZ3.append(Int(intVar))
        for floatVar in floatVars:
            self.floatVarsZ3.append(Real(floatVar))
        for boolVar in boolVars:
            self.boolVarsZ3.append(Bool(boolVar))

        self.relations = relations

    def createNegationPredicates(self):
        negationPredictes = []
        for boolVarZ3 in self.boolVarsZ3:
            negationPredictes.append(Not(boolVarZ3))
        return negationPredictes
    
    def createEqualityBooleanPredicates(self):
        equalityBooleanPredicates = []
        if len(self.boolVarsZ3) >= 2:
            allCombinations = itertools.combinations(self.boolVarsZ3, 2)
            for (var1, var2) in allCombinations:
                equalityZ3 = var1 == var2
                equalityBooleanPredicates.append(equalityZ3)
                equalityBooleanPredicates.append(Not(equalityZ3))
        return equalityBooleanPredicates
    
    def createEqualityIntPredicates(self):
        equalityIntPredicates = []
        if len(self.intVarsZ3) >= 2:
            allCombination = itertools.combinations(self.intVarsZ3, 2)
            for (var1, var2) in allCombination:
                equalityZ3 = var1 == var2
                equalityIntPredicates.append(equalityZ3)
                equalityIntPredicates.append(Not(equalityZ3))  
        return equalityIntPredicates
    
    def createEqualityFloatPredicates(self):
        equalityFloatPredicates = []
        if len(self.floatVarsZ3) >= 2:
            allCombination = itertools.combinations(self.floatVarsZ3, 2)
            for (var1, var2) in allCombination:
                equalityZ3 = var1 == var2
                equalityFloatPredicates.append(equalityZ3)
                equalityFloatPredicates.append(Not(equalityZ3))  
        return equalityFloatPredicates

if __name__ == '__main__':
    p = Problem(['s.Count', 's.Capacity'], [], ['s.Contains(x)', 's.Contains(y)'], [])
    print(p.intVarsZ3[0])
    print(p.boolVarsZ3[1])
    tmp = p.createEqualityIntPredicates()
    print(tmp[1])