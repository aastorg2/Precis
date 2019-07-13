from z3 import *
from precis_feature import PrecisFeature

class FeatureVector:

    # tuple of z3 values 
    valuesZ3 = ()
    # tuple of strings representing values of features (i.e represents a row of data; a list of self.values would represent a 2D matrix.)
    values = ()
    
    

    def __init__(self, precisFeatureList, values, testLabel):
        self.values = values

        # boolean value indices
        self.boolFeatureIndices = []

        assert(testLabel == 'True' or testLabel == 'False')
        for idx in range(len(values)):
            self.AddValues(precisFeatureList[idx].varZ3, values[idx], idx)
        
        if testLabel == 'True':
            self.testLabel = True
        else:
            self.testLabel = False

        #TODO: counterexample label should not set here but at client side
        self.counterexampleLabel = True

    def AddValues(self, precisFeatureZ3, value, idx):
        self.CheckValueType(precisFeatureZ3, value)
        if is_int(precisFeatureZ3):
            self.valuesZ3 += (IntVal(value), )
        elif is_real(precisFeatureZ3):
            self.valuesZ3 += (RealVal(value), )
        elif is_bool(precisFeatureZ3):
            self.valuesZ3 += (BoolVal(value.upper() == 'TRUE'), )
            self.boolFeatureIndices.append(idx)

    # DEBUG method
    def CheckValueType(self, precisFeatureZ3, value):
        # Check int
        assert((type(eval(value)) == int) == is_int(precisFeatureZ3))
        # Check float
        assert((type(eval(value)) == float) == is_real(precisFeatureZ3))
        # Check bool
        assert(((value.upper() == 'TRUE') or (value.upper() == 'FALSE')) == is_bool(precisFeatureZ3))
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
    
    def __getitem__(self, key):
        return self.valuesZ3[key]

    def __setitem__(self, key, value):
        pass
        
    def __len__(self):
        return len(self.valuesZ3)

    # derivedValuesZ3: tuple of derived Z3 values
    def __add__(self, derivedValuesZ3):
        derivedValues = ()
        for valueZ3 in derivedValuesZ3:
            derivedValues += (str(valueZ3), )
        featureVector = FeatureVector([], [], str(self.testLabel))
        featureVector.values = self.values + derivedValues
        featureVector.valuesZ3 = self.valuesZ3 + derivedValuesZ3
        featureVector.boolFeatureIndices = self.boolFeatureIndices + list(range(len(self.values), len(self.values) + len(derivedValues)))
        return featureVector