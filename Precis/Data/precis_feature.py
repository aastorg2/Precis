from z3 import *

class PrecisFeature:

    # varName: string; variable name
    varName = ""
    # isNew: string; True: New_*, False, Old_*, None: feature is derived
    isNew = None
    # varZ3: Z3ExprRef; variable of Z3 version
    varZ3 = None
    # isDerived: bool; whether the feature is derived
    isDerived = None
    
    # isDerived: bool
    # varName: string; variable name
    # varType: string; {int, float, bool}, declared when the feature is not derived
    # isNew: bool; declared when the feature is not derived
    # varZ3: Z3ExprRef; declared when the feature is derived
    def __init__(self, isDerived, varName, varType=None, isNew=None, varZ3=None):
        
        if isDerived:
            # Check variable type
            self.CheckVarType(varType)

            self.varName = str(varZ3)
            self.isNew = isNew
            self.varZ3 = varZ3
            self.isDerived = True
        else: # base feature -> from parameterized unit test
            # Check variable type
            self.CheckVarType(varType)

            self.varName = varName
            self.isNew = isNew
            self.isDerived = False

            if varType.upper() == 'INT':
                self.varZ3 = Int(varName)
            elif varType.upper() == 'FLOAT':
                self.varZ3 = Real(varName)
            elif varType.upper() == 'BOOL':
                self.varZ3 = Bool(varName)
            else:
                raise Exception('Unknown type!')
            
    # DEBUG method
    def CheckVarType(self, varType):
        assert varType.upper() == 'INT' or varType.upper() == 'FLOAT' or varType.upper() == 'BOOL', 'Only variables with type int, float and bool are supported!!!'

    def __str__(self):
        return self.varName
    
    # for printing PrecisFeature in Lists
    def __repr__(self):
        return self.__str__()
    
    def __eq__(self, otherFeature):
        hasattr(otherFeature, 'varZ3') and hasattr(otherFeature, 'varName') and self.varZ3.eq(otherFeature.varZ3)

    def __hash__(self):
        return self.varZ3.hash() 

if __name__ == '__main__':
    precisFeature = PrecisFeature(False, 'New_s1Count', 'Int', True, None)
    print(precisFeature)  
