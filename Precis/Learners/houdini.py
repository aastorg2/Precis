from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class Houdini:
    
    useBounds = False


    def generateDerivedFeatureVectors(self, derivedFeatures, features, featureVectors):
        deriveFeatureVec = ()
        print(derivedFeatures)
        print(featureVectors)
        print ("here")
        print(features)

        #TODO: f of type FeatureVector --> make this indexable; this line wont work
        #print(features[i], f[i])
        for f in featureVectors:
            print(f)
            print (type(f))
            for i in  range(len(features)):
                #print(features[i])
                #print(f.valuesZ3[i]) # this will throw index out range
                print(features[i], f[i])

        print(type(deriveFeatureVec))

    def learn(featureVector):
        pass
