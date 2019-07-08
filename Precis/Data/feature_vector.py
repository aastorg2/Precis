from z3 import *
from precis_feature import PrecisFeature

class FeatureVector:

    #tuple of z3 values 
    #valuesZ3 = ()

    #tuple of values(in string format) 

    def __init__(self, pvarList, values, testLabel):
        #represents a row of data; a list of self.values would represent a 2D matrix.

        #self.values = values[:-1]
        self.values = values
        assert(testLabel == 'True' or testLabel == 'False')
        self.valuesZ3 = ()
        #TODO: why range(len(values) -1 )
        for idx in range(len(values) - 1):
        #for idx in range(len(values)):
        #for idx in range(len(pvarList)):
            self.AddValues(pvarList[idx].varZ3, values[idx])
        
        if testLabel == 'True':
            self.testLabel = True
        else:
            self.testLabel = False

        #TODO: counterexample label should not set here but at client side
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