from z3 import *
from precis_feature import PrecisFeature

class FeatureVector:

    #tuple of z3 values 
    valuesZ3 = ()

    #tuple of values(in string format) 

    def __init__(self, pvarList, values, testLabel):
        # In 2d matrix, represents a row of data
        #self.values = values[:-1]
        assert(testLabel == 'True' or testLabel == 'False')

        self.values = values
        
        #self.valuesZ3 = ()
        for idx in range(len(values) - 1):
            self.AddValues(pvarList[idx].varZ3, values[idx])
        
        if testLabel == 'True':
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
    # End of DEBUG method

    def __str__(self):
        output = '('
        for value in self.values:
            output += value + ', '
        output += str(self.testLabel) + ', '
        output += str(self.counterexampleLabel) + ')'
        return output
    
    # for printing FeatureVector in Lists
    def __repr__(self):
        return self.__str__()