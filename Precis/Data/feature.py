from z3 import *
from precis_feature import *

class Feature:
    def __init__(self, pVar):
        # feature
        self.pVar = pVar
        
        # values of feature
        # in 2d matrix representation of feature vectors, this is a column.
        self.values = tuple()
        self.valuesZ3 = tuple()

    # values (list of string): list of values 
    def AddValues(self, values):
        for value in values:
            self.values += (value,)

            self.CheckValueType(self.pVar.varZ3, value)
            if is_int(self.pVar.varZ3):
                self.valuesZ3 += (IntVal(value),)
            elif is_real(self.pVar.varZ3):
                self.valuesZ3 += (RealVal(value),)
            elif is_bool(self.pVar.varZ3):
                self.valuesZ3 += (BoolVal(value),)

    def ClearValues(self):
        self.values = tuple()
        self.valuesZ3 = tuple()

    # DEBUG method
    def CheckValueType(self, var, value):
        # Check int
        assert((type(eval(value)) == int) == is_int(self.pVar.varZ3))
        # Check float
        assert((type(eval(value)) == float) == is_real(self.pVar.varZ3))
        # Check bool
        assert(((value.upper() == 'TRUE') or (value.upper() == 'FALSE')) == is_bool(self.pVar.varZ3))

if __name__ == '__main__':
    a = 'New_s1Count'
    b = ['1', '2', '3']
    pVar = PrecisFeature(a, 'int', a.startswith('New_'))
    dp = Feature(pVar)
    print(len(dp.valuesZ3))
    dp.AddValues(b)
    print(len(dp.valuesZ3))
    dp.ClearValues()
    print(len(dp.valuesZ3))