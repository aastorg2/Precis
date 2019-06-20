import itertools
from z3 import *

class Problem:
    def __init__(self, intVars, floatVars, boolVars, relations):
        self.intVars = intVars
        self.floatVars = floatVars
        self.boolVars = boolVars

        self.intVarsZ3 = []
        self.floatVarsZ3 = []
        self.boolVarsZ3 = []

        for intVar in self.intVars:
            self.intVarsZ3.append(Int(intVar))
        for floatVar in self.floatVars:
            self.floatVarsZ3.append(Real(floatVar))
        for boolVar in self.boolVars:
            self.boolVarsZ3.append(Bool(boolVar))

        self.relations = relations

    def createNegationPredicates(self):
        negationPredictes = []
        for boolVarZ3 in self.boolVarsZ3:
            negationPredictes.append(Not(boolVarZ3))
        return negationPredictes
    
    def createEqualityBooleanPredicates(self):
        equalityBooleanPredicates = []
        if len(self.boolVars) >= 2:
            all_combination = itertools.combinations(self.boolVars, 2)
            for (var1, var2) in all_combination:
                equalityZ3 = Bool(var1 + '==' + var2)
                equalityBooleanPredicates.append(equalityZ3)
                equalityBooleanPredicates.append(Not(equalityZ3))
        return equalityBooleanPredicates
        

if __name__ == '__main__':
    p = Problem(['s.Count', 's.Capacity'], [], ['s.Contains(x)', 's.Contains(y)'], [])
    print(p.intVarsZ3[0])
    print(p.boolVarsZ3[1])
    tmp = p.createEqualityBooleanPredicates()
    print(tmp[1])