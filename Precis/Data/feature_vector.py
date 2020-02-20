from z3 import *
from precis_feature import PrecisFeature
from typing import Type

class FeatureVector:

    # tuple of z3 values 
    valuesZ3 = ()
    # tuple of strings representing values of features (i.e represents a row of data; a list of self.values would represent a 2D matrix.)
    values = ()
    #passing or failing test
    testLabel = None
    #kinds = ()
    #TODO: need a way to construct a FeatureVector where the values are already Z3 boolref values

    def __init__(self, precisFeatureList, values, testLabel):
        self.values = values

        assert(testLabel == 'True' or testLabel == 'False')
        assert( len(precisFeatureList) == len(values) )
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
    
    @staticmethod
    def copyFeatureVector(fv : 'FeatureVector'): 
        if not isinstance(fv, FeatureVector):
            assert False, "type of parameter fv is not FeatureVector"
        else:
            newFV = FeatureVector([], [], str(fv.testLabel))
            newFV.values = tuple(fv.values)
            newFV.valuesZ3 = tuple(fv.valuesZ3)
            return newFV

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
        output += "TL="+str(self.testLabel) + ', '
        output += "L="+str(self.counterexampleLabel) + ')'
        return output
    
    #def toString(self):
    #    output = '('

    # for printing FeatureVector in Lists
    def __repr__(self):
        return self.__str__()
    
    def __getitem__(self, key):
        return self.valuesZ3[key]

    def __setitem__(self, key, value):
        pass
        
    def __len__(self):
        return len(self.valuesZ3)

    def __eq__(self, other):
        return hasattr(other, 'valuesZ3') and hasattr(other, 'values') and self.testLabel == other.testLabel \
             and self.valuesZ3 == other.valuesZ3 # tuple equiality

    def __hash__(self):
        return hash(self.valuesZ3)

    # derivedValuesZ3: tuple of derived Z3 values
    """
    def __add__(self, derivedValuesZ3):
        derivedValues = ()
        for valueZ3 in derivedValuesZ3:
            derivedValues += (str(valueZ3), )
        featureVector = FeatureVector([], [], str(self.testLabel))
        featureVector.values = self.values + derivedValues
        featureVector.valuesZ3 = self.valuesZ3 + derivedValuesZ3
        return featureVector
    """
    
     # otherFV: other feature vector
    def __add__(self, otherFV):
        assert(otherFV.testLabel == self.testLabel)
        featureVector = FeatureVector([], [], str(self.testLabel))
        featureVector.values = self.values + otherFV.values
        featureVector.valuesZ3 = self.valuesZ3 + otherFV.valuesZ3
        return featureVector