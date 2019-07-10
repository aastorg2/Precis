from z3 import *
import itertools
from Data.precis_feature import PrecisFeature

class Houdini:
    
    useBounds = False


    def generateDerivedFeatureVectors(self, derivedFeatures, baseFeatures, featureVectors):
        
        print(derivedFeatures)
        print(featureVectors)
        print ("here")
        print(baseFeatures)
        pairs = list()
        # consider
        for f in featureVectors:
            print("feature vec: " +str(f))
            pairs = Houdini.generateFeatureValueMapping(baseFeatures,f)
            print(pairs)
            #print(type(pairs))
            for df in derivedFeatures:
                #TODO: the substitute does not work
                #t = simplify(And(df.varZ3,pairs[0][0] == pairs[0][1],pairs[1][0] == pairs[1][1])) ideally simplify should evaluate AND(x != y, x ==2, y == 3) to false
                #print("print simplify " + str(t))
                subDf = substitute(df.varZ3 , pairs)
                print(simplify(subDf) )
                #print(type(df.varZ3))

        #for df in derivedFeatures:
        #    print(df)

    @staticmethod
    def generateFeatureValueMapping(baseFeatures, featureVector):
        pairs = list()
        # consider removing check for perfomances in cases where the number of feature vectors gets large.
        # number of base features should be the same as the number of entries in feature vector(values of said features)
        assert(len(featureVector) == len(baseFeatures))
        for i in  range(len(baseFeatures)):
            #print("type of featVec", type(featureVector[i]))
            pair = (baseFeatures[i].varZ3 , featureVector[i])
            pairs.append(pair)
        return pairs


    def learn(featureVector):
        pass
