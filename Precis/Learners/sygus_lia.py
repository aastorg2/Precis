from Learners.sygus import Sygus
from os import sys, path

class SygusLIA(Sygus):
    
    def __init__(self, execBin):
        super().__init__(execBin)

    #Todo: handle case for boolean feature vectors
    def constructGrammar(self, intFeatures, boolFeatures):
        #getting old variables(pre-states)
        intStr = list((map(lambda x:  str(x) , intFeatures)))
        #intStr = list((map(lambda x:  str(x) , intFeatures)))
        #boolStr = [ str(x) for x in boolFeatures if x.isNew != None and not(x.isNew)]
        #boolStr = list((map(lambda x:  str(x), boolFeatures)))
        #boolDecl = list((map(lambda x: "(" + x + " Bool)", boolStr)))
        intDecl = list((map(lambda x: "(" + x + " Int)", intStr)))
        
        intConsts = ["0", "1"]
        #boolConsts = ["true", "false"]
        
        synthFuncDecl = "synth-fun Postcondition"

        startSymbolInt = ["(", "Start",  "Int",  "(StartInt)", ")"]
        intArithProductions = [["(+ StartInt StartInt)"], ["(- StartInt StartInt)"]] #, ["(ite StartBool StartInt StartInt)"]]
        #intCompareProductions = [["(<=  StartInt StartInt)"], ["(= StartInt StartInt)"], ["(>=  StartInt StartInt)"]]
        #boolProductions = [["(and StartBool StartBool)"], ["(or StartBool StartBool)"], ["(not StartBool)"]]

        intGrammar =[  ["(", "StartInt", "Int", "("],
                       [intConsts],
                       [intStr],
                       intArithProductions,
                       [")", ")"]
        ]

        grammar = [  [ "(", synthFuncDecl,"("] +  intDecl + [")", "Int", "(" ],
                     [startSymbolInt],
                     intGrammar,
                     [ ")", ")"]
                  ]
        return grammar

    def addSemanticConstraints(self, idxNewFeature, oldFeaturesIdxs , featureVectors):
        
        if not (all(oldFeaturesIdxs[i][1] <= oldFeaturesIdxs[i+1][1] for i in range(len(oldFeaturesIdxs)-1))):
            oldFeaturesIdxs = sorted(oldFeaturesIdxs, key=lambda tup: tup[1])
        
        constraints = []
        for fv in featureVectors:
            oldFeatureValues = [ fv[i[1]] for i in oldFeaturesIdxs]
            #print(oldFeatureValues)
            fnCall =  ["(", "= ", "(", "Postcondition"]  +  oldFeatureValues + [ ")", fv[idxNewFeature], ")"]
            #print(fnCall)
            constraints.append(["(", "constraint"] + fnCall + [")"])
        return constraints