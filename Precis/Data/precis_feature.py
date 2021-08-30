from z3 import *




class PrecisFeature:
    # Python notes: variables declared outside method by inside class are "class variables"
    # those declared inside __init__ method as instance variables.
    # class variable is updated
    #ID = 0
    
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
            if "New_arrListLastIndexOfX ==" in varName:
                print()
            self.varName = varName
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
            #refactor ObserverExtractor so that when it sees a float type (in C#), it outputs REAL as its type in typeOM.txt
            elif varType.upper() == 'FLOAT' or varType.upper() == 'REAL':
                self.varZ3 = Real(varName)
            elif varType.upper() == 'BOOL':
                self.varZ3 = Bool(varName)
            else:
                raise Exception('Unknown type!')

        #FreshInt gets unique constant with respect to context
        #atom: name of literal identifier
        #if self.atom == None:
        arithRefId = FreshInt("cond")
        self.atom = str(arithRefId).replace("!","")

    # DEBUG method
    def CheckVarType(self, varType):
        assert varType.upper() == 'INT' or varType.upper() == 'FLOAT' or varType.upper() == 'REAL' or varType.upper() == 'BOOL', 'Only variables with type int, float and bool are supported!!!'

    def __str__(self):
        return self.varName
    
    # for printing PrecisFeature in Lists
    def __repr__(self):
        return self.__str__()
    
    #TODO: consider implementing equality that checks Ast equality
    def __eq__(self, otherFeature):
        # eq(simplify(self.varZ3), simplify(otherFeature.varZ3)) --> so that 1+x
        return hasattr(otherFeature, 'varZ3') and hasattr(otherFeature, 'varName') and (eq(self.varZ3, otherFeature.varZ3) \
            or (eq(self.varZ3.decl(), otherFeature.varZ3.decl()) and (set(self.varZ3.children()) == set(otherFeature.varZ3.children()))  )  )

    def __hash__(self):
        return self.varZ3.hash() 

if __name__ == '__main__':
    precisFeature = PrecisFeature(False, 'New_s1Count', 'Int', True, None)
    print(precisFeature)  
