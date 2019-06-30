from z3 import *
from precis_feature import PrecisFeature

class FeatureVector:
    def __init__(self, pvarList, values):
        # In 2d matrix, represents a row of data
        self.values = values[:-1]
        self.valuesZ3 = ()
        for idx in range(len(values) - 1):
            self.AddValues(pvarList[idx].varZ3, values[idx])
        assert(values[-1] == 'True' or values[-1] == 'False')
        
        if values[-1] == 'True':
            self.testLabel = True
        else:
            self.testLabel = False

        self.counterexampleLabel = True

    def AddValues(self, pvarZ3, value):
        self.CheckValueType(pvarZ3, value)
        if is_int(pvarZ3):
            self.valuesZ3 += (IntVal(value), )
        elif is_real(pvarZ3):
            self.valuesZ3 += (RealVal(value), )
        elif is_bool(pvarZ3):
            self.valuesZ3 += (BoolVal(value), )

    # DEBUG method
    def CheckValueType(self, pvarZ3, value):
        # Check int
        assert((type(eval(value)) == int) == is_int(pvarZ3))
        # Check float
        assert((type(eval(value)) == float) == is_real(pvarZ3))
        # Check bool
        assert(((value.upper() == 'TRUE') or (value.upper() == 'FALSE')) == is_bool(pvarZ3))
    
    def __str__(self):
        output = '('
        for value in self.values:
            output += value + ', '
        output += str(self.testLabel) + ', '
        output += str(self.counterexampleLabel) + ')'
        return output