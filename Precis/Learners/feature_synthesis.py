from z3 import *
import itertools

from Learners.sygus_lia import SygusLIA
from Data.precis_feature import PrecisFeature
from Learners.sygus import Sygus
from os import sys, path
from Data.shell import Shell

from typing import List, Tuple
class FeatureSynthesis:

    #binary executable to run sygus solver
    binary = ""
    temporaryFolder = ""
    sygusFileEndingPattern = '.*\.sl'
    sygusFileName = ""
    # list of base features used to generate predicates and synthesize feature using a grammars
    baseFeatures: Tuple[PrecisFeature] = None
    baseFeatureVectors = None
    
    def __init__(self, binaryExec, tempFolder, syguFileName):
        #assert (baseFeatures != None)
        self.binary = binaryExec
        self.temporaryFolder = tempFolder
        self.sygusFileName = syguFileName

    def updateBaseFeatureVector(self, baseFv):
        self.baseFeatureVectors = baseFv

    def updateBaseFeatures(self, features):
        self.baseFeatures = features

    def GenerateDerivedFeatures(self,intFeat, boolFeat):
        #intFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Int"]
        #boolFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Bool"]
        intFeatures = intFeat
        boolFeatures = boolFeat
        negationBaseBoolFeatures =()
        derivedFeatures = ()
        assert(len(intFeatures) > 0)
        #assert(len(boolFeatures) > 0)
        derivedFeatures: Tuple[PrecisFeature] = derivedFeatures + self.CreateInequalities(intFeatures)
        derivedFeatures: Tuple[PrecisFeature] = self.CreateEqualities(intFeatures)
        derivedFeatures: Tuple[PrecisFeature] = derivedFeatures + self.CreateEqualitiesWithConstants(intFeatures)
        derivedFeatures: Tuple[PrecisFeature] = derivedFeatures + self.CreateInequalitiesWithConstants(intFeatures)
        #temporarily changed order
        if len(boolFeatures) > 0: # there exist any base bool observer methods
            pass # do not create negation to reduce space of formulas DT synthesizer has to explore
            #negationBaseBoolFeatures: Tuple[PrecisFeature] = self.createNegationBool(boolFeatures)
        
        return negationBaseBoolFeatures + derivedFeatures
        #return derivedFeatures
        #Todo: call to sygus solvers can be placed here.
    def synthesizeFeatures(self,intFeat, boolFeat, baseFeatureVectors):
        #assert( baseFeatureVectors != None)
        #intFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Int"]
        #boolFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Bool"]
        intFeatures = intFeat
        boolFeatures = boolFeat
        grammar = ""
        assert(len(intFeatures) > 0)

        sygusSynthesizer = SygusLIA(self.binary)
        #grammar = sygusSynthesizer.formatGrammar(sygusSynthesizer.constructGrammar(intFeatures, boolFeatures))
        
        #getting old vars
        intOldVarAndIdxs = [(intFeatures[idx],idx) for idx in range(len(intFeatures)) if intFeatures[idx].isNew != None and not(intFeatures[idx].isNew)]
        intOldVarFeatures = list((map(lambda x:  x[0] , intOldVarAndIdxs))) # map applies function(x[0], accessor) to iterable(list, tuple,etc) inputs(intOldVarAndIdxs). 
        #print(sygusSynthesizer.formatGrammar(grammar))
        if len(intOldVarFeatures) == 0:
            return ()
        shell = Shell(True)

        ## wrap this code with a synthesize function
        ## there can be synthesized features that we already add
        logic = [["(set-logic LIA)"]]
        checkSynth = [["(check-synth)"]]
        synthesizedFeatures = ()
        for postFeaturesIdxs  in [ (intFeatures[newIdx], newIdx) for newIdx in range(len(intFeatures)) if intFeatures[newIdx].isNew != None and intFeatures[newIdx].isNew]:
            #print(postFeaturesIdxs[0].varName)
            shell.removeSygusFile(self.temporaryFolder, self.sygusFileEndingPattern)
            # Don't need bool features
            grammar = sygusSynthesizer.constructGrammar(intOldVarFeatures, boolFeatures)
            constraints = sygusSynthesizer.addSemanticConstraints(postFeaturesIdxs[1],intOldVarAndIdxs, baseFeatureVectors)
            sygusProblem = sygusSynthesizer.constructSygusProblem(logic, grammar, constraints,checkSynth)
            shell.writeToFile(self.temporaryFolder,self.sygusFileName, sygusProblem )
            synthizedExprStr = sygusSynthesizer.learn(self.temporaryFolder,self.sygusFileName)
            if synthizedExprStr == "No Solutions!":
                print("no solution synthesis")
                continue
            declMap = { f.varName : f.varZ3 for f in intFeatures}
            synthesizedFeature = "(= "+ postFeaturesIdxs[0].varName +" " +synthizedExprStr +")" 
            sygusExpr = parse_smt2_string("(assert "+ synthesizedFeature+ " )",decls=declMap)
            print("======================= synthesized feature: "+ str(sygusExpr[0]))
            synthesizedFeatures += (PrecisFeature(True, str(sygusExpr[0]), str(sygusExpr[0].sort()), None, sygusExpr[0]),)#assumes only return list of length == 1(sygusExpr) 
            #print(sygusExpr.ctx)
            #print(postFeaturesIdxs[0].varZ3.ctx)
        #print(synthesizedFeatures)
        return synthesizedFeatures




    def createNegationBool(self, boolFeatures):
        negBoolFeatures = ()
        for bf in boolFeatures:
            negBoolExpr = Not(bf.varZ3)
            negBoolDerive = PrecisFeature(True, str(negBoolExpr), str(negBoolExpr.sort()), None, negBoolExpr)
            negBoolFeatures += (negBoolDerive,)
        return negBoolFeatures

    # CreateInequalities and Equalities are code clones.
    def CreateInequalities(self, intFeatures):
        inequalitiesFeatures = ()
        if len(intFeatures) <= 1:
            return ()
        allCombinations = itertools.combinations(intFeatures,2)
        for (feat1,feat2) in allCombinations:
            #if feat1.isNew == False and feat2.isNew == False:# skip comparison among variables of the pre state only
            #    continue
            lessThanExpr = feat2.varZ3 < feat1.varZ3
            lessThanExprReversed = feat1.varZ3 < feat2.varZ3
            lessThanEqualExpr = feat2.varZ3 <= feat1.varZ3
            #lessThanEqualExprReversed = feat1.varZ3 <= feat2.varZ3
            
            lessThanDerived = PrecisFeature(True, str(lessThanExpr), str(lessThanExpr.sort()), None, lessThanExpr)
            lessThanEqualDerived = PrecisFeature(True, str(lessThanEqualExpr), str(lessThanEqualExpr.sort()), None, lessThanEqualExpr)
            lessThanDerivedRev = PrecisFeature(True, str(lessThanExprReversed), str(lessThanExprReversed.sort()), None, lessThanExprReversed)
            #lessThanEqualDerivedRev = PrecisFeature(True, str(lessThanEqualExprReversed), str(lessThanEqualExprReversed.sort()), None, lessThanEqualExprReversed)
            inequalitiesFeatures += (lessThanDerived,)
            inequalitiesFeatures += (lessThanEqualDerived,)
            inequalitiesFeatures += (lessThanDerivedRev,)
            #inequalitiesFeatures += (lessThanEqualDerivedRev,)
            
        return inequalitiesFeatures

    # this method assumes it called with integer features
    def CreateEqualities(self, intFeatures):
        equalitiesFeatures = ()        
        
        if len(intFeatures) <= 1:
            return ()
            #return intFeatures # throw new error
        
        allCombinations = itertools.combinations(intFeatures,2)
        
        for (feat1,feat2) in allCombinations:
            #if feat1.isNew == False and feat2.isNew == False: # skip comparison among variables of the pre state only
            #    continue
            #print (feat1, feat2)
            #removing negation of equalities for now
            #notEqualExpr = feat2.varZ3 != feat1.varZ3 
            equalExpr = feat2.varZ3  == feat1.varZ3 
            #print(notEqualExpr)
            #print(notEqualExpr.sort())
            #print(type(notEqualExpr))
            #notEqualDerived = PrecisFeature(True, str(notEqualExpr), str(notEqualExpr.sort()), None, notEqualExpr)
            equalDerived = PrecisFeature(True, str(equalExpr), str(equalExpr.sort()), None, equalExpr)
            #equalitiesFeatures += (notEqualDerived,)
            equalitiesFeatures += (equalDerived,)
        return equalitiesFeatures

    def CreateEqualitiesWithConstants(self, intFeatures):
        equalitiesWithConstantsFeatures = ()        
        
        if len(intFeatures) == 0:
            return ()
            #return intFeatures # throw new error
        
        for feat1 in intFeatures:
            #print (feat1, feat2)
            equalOneExpr = feat1.varZ3 == IntVal(1)
            equalZeroExpr = feat1.varZ3 == IntVal(0)
            equalNegOneExpr = feat1.varZ3 == IntVal(-1)
            #print(notEqualExpr)
            #print(notEqualExpr.sort())
            #print(type(notEqualExpr))
            equalOneExpr = PrecisFeature(True, str(equalOneExpr), str(equalOneExpr.sort()), None, equalOneExpr)
            equalZeroExpr = PrecisFeature(True, str(equalZeroExpr), str(equalZeroExpr.sort()), None, equalZeroExpr)
            equalNegOneExpr = PrecisFeature(True, str(equalNegOneExpr), str(equalNegOneExpr.sort()), None, equalNegOneExpr)
            equalitiesWithConstantsFeatures += (equalNegOneExpr,)
            equalitiesWithConstantsFeatures += (equalOneExpr,)
            equalitiesWithConstantsFeatures += (equalZeroExpr,)
        return equalitiesWithConstantsFeatures

    def CreateInequalitiesWithConstants(self, intFeatures):
        inequalitiesWithConstantsFeatures = ()        
        
        if len(intFeatures) == 0:
            return ()
            #return intFeatures # throw new error
        
        for feat1 in intFeatures:
            #print (feat1, feat2)
            greaterThanOneExpr = feat1.varZ3 > IntVal(1)
            greaterThanEqualOneExpr = feat1.varZ3 >= IntVal(1)
            greaterThanZeroExpr = feat1.varZ3 > IntVal(0)
            greaterThanEqualZeroExpr = feat1.varZ3 >= IntVal(0)
            greaterThanNegOneExpr = feat1.varZ3 > IntVal(-1)
            greaterThanEqualNegOneExpr = feat1.varZ3 >= IntVal(-1)
            #print(notEqualExpr)
            #print(notEqualExpr.sort())
            #print(type(notEqualExpr))
            greaterThanOneExpr = PrecisFeature(True, str(greaterThanOneExpr), str(greaterThanOneExpr.sort()), None, greaterThanOneExpr)
            greaterThanEqualOneExpr = PrecisFeature(True, str(greaterThanEqualOneExpr), str(greaterThanEqualOneExpr.sort()), None, greaterThanEqualOneExpr)
            greaterThanZeroExpr = PrecisFeature(True, str(greaterThanZeroExpr), str(greaterThanZeroExpr.sort()), None, greaterThanZeroExpr)
            greaterThanEqualZeroExpr = PrecisFeature(True, str(greaterThanEqualZeroExpr), str(greaterThanEqualZeroExpr.sort()), None, greaterThanEqualZeroExpr)
            greaterThanNegOneExpr = PrecisFeature(True, str(greaterThanNegOneExpr), str(greaterThanNegOneExpr.sort()), None, greaterThanNegOneExpr)
            greaterThanEqualNegOneExpr = PrecisFeature(True, str(greaterThanEqualNegOneExpr), str(greaterThanEqualNegOneExpr.sort()), None, greaterThanEqualNegOneExpr)
            inequalitiesWithConstantsFeatures += (greaterThanOneExpr,)
            inequalitiesWithConstantsFeatures += (greaterThanEqualOneExpr,)
            inequalitiesWithConstantsFeatures += (greaterThanZeroExpr,)
            inequalitiesWithConstantsFeatures += (greaterThanEqualZeroExpr,)
            inequalitiesWithConstantsFeatures += (greaterThanNegOneExpr,)
            inequalitiesWithConstantsFeatures += (greaterThanEqualNegOneExpr,)
        return inequalitiesWithConstantsFeatures
    