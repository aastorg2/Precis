from z3 import *

class Datapoint:
    # var (string): variable name
    # varType (string): variable type, int|float|bool
    def __init__(self, var, varType):
        self.checkVarType(varType)

        if varType.upper() == 'INT':
            self.varZ3 = Int(var)
        elif varType.upper() == 'FLOAT':
            self.varZ3 = Real(var)
        elif varType.upper() == 'BOOL':
            self.varZ3 = Bool(var)
        
        self.valuesZ3 = []

    # values (list of string): list of values 
    def addValues(self, values):
        for value in values:
            self.checkValueType(self.varZ3, value)
            
            if is_int(self.varZ3):
                self.valuesZ3.append(IntVal(value))
            elif is_real(self.varZ3):
                self.valuesZ3.append(RealVal(value))
            elif is_bool(self.varZ3):
                self.valuesZ3.append(BoolVal(value))

    def clearValues(self):
        self.valuesZ3 = []

    def checkVarType(self, varType):
        assert(varType.upper() == 'INT' or varType.upper() == 'FLOAT' or varType.upper() == 'BOOL')

    def checkValueType(self, var, value):
        # Check int
        assert((type(eval(value)) == int) == is_int(var))
        # Check float
        assert((type(eval(value)) == float) == is_real(var))
        # Check bool
        assert(((value.upper() == 'TRUE') or (value.upper() == 'FALSE')) == is_bool(var))

if __name__ == '__main__':
    a = 'a'
    b = ['1', '2', '3']
    
    dp = Datapoint(a, 'Int')
    print(len(dp.valuesZ3))
    dp.addValues(b)
    print(len(dp.valuesZ3))
    dp.clearValues()
    print(len(dp.valuesZ3))