from z3 import *

class PrecisFeature:

    #string
    varName = ""
    #bool should isNew be none for when PrecisFeature is derived?
    isNew = False
    #Z3ExprRef
    varZ3 = None
    isDerived = None
    #TODO: need an additional field -- isDerived = derived predicates

    # TODO: Need to add isDerived to parameter
    def __init__(self, varName, varType, isNew=None):
        # Check variable type
        self.CheckVarType(varType)

        self.varName = varName  # string version of var
        self.isNew = isNew

        if varType.upper() == 'INT':
            self.varZ3 = Int(varName)
        elif varType.upper() == 'FLOAT':
            self.varZ3 = Real(varName)
        elif varType.upper() == 'BOOL':
            self.varZ3 = Bool(varName)
        else:
            print('Unknown type!')
            exit(1)# throw exception instead of abruptly exiting
        
        isDerived = False
    
    @staticmethod
    def create(isDerived, z3DerivedFeatExpr, tpe=""):
        precisFeature = PrecisFeature(str(z3DerivedFeatExpr), tpe, None)
        precisFeature.isDerived = True
        
        precisFeature.varZ3 = z3DerivedFeatExpr

        return precisFeature
        
    #         self.isNew = None
    #     self.varName = str(z3DerivedFeatExpr)
    #     self.isDerived = isDerived


    # DEBUG method
    def CheckVarType(self, varType):
        assert varType.upper() == 'INT' or varType.upper() == 'FLOAT' or varType.upper() == 'BOOL', 'Only variables with type int, float and bool are supported!!!'
    
    def __str__(self):
        return self.varName
    
    # for printing PrecisFeature in Lists
    def __repr__(self):
        return self.__str__()

if __name__ == '__main__':
    pvar = PrecisFeature('New_s1Count', 'Int', True)
    print(pvar)
