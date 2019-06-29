from z3 import *
from precis_var import *

class Datapoint:
    def __init__(self, pVar):
        # feature
        self.pVar = pVar
        
        # values of feature
        # in 2d matrix representation of feature vectors, this is a column.
        self.values = []
        self.valuesZ3 = []

    # values (list of string): list of values 
    def addValues(self, values):
        for value in values:
            self.values.append(value)

            self.checkValueType(self.pVar.varZ3, value)
            if is_int(self.pVar.varZ3):
                self.valuesZ3.append(IntVal(value))
            elif is_real(self.pVar.varZ3):
                self.valuesZ3.append(RealVal(value))
            elif is_bool(self.pVar.varZ3):
                self.valuesZ3.append(BoolVal(value))

    def clearValues(self):
        self.values = []
        self.valuesZ3 = []

    # DEBUG method
    def checkValueType(self, var, value):
        # Check int
        assert((type(eval(value)) == int) == is_int(self.pVar.varZ3))
        # Check float
        assert((type(eval(value)) == float) == is_real(self.pVar.varZ3))
        # Check bool
        assert(((value.upper() == 'TRUE') or (value.upper() == 'FALSE')) == is_bool(self.pVar.varZ3))

if __name__ == '__main__':
    a = 'New_s1Count'
    b = ['1', '2', '3']
    pVar = PrecisVar(a, 'int', a.startswith('New_'))
    dp = Datapoint(pVar)
    print(len(dp.valuesZ3))
    dp.addValues(b)
    print(len(dp.valuesZ3))
    dp.clearValues()
    print(len(dp.valuesZ3))