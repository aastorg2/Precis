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
        
        
        for f in featureVectors:
            # consider removing check for perfomances in cases where the number of feature vectors gets large.
            # number of base features should be the same as the number of entries in feature vector(values of said features)
            assert(len(f) == len(features))
             
            print("feature vec: " +str(f))
            pairs = list()
            for i in  range(len(features)):
                pair = (features[i], f[i])
                pairs.append(pair)
            print(pairs)
        
        print(type(deriveFeatureVec))

        #for df in derivedFeatures:
        #    print(df)

    def learn(featureVector):
        pass
