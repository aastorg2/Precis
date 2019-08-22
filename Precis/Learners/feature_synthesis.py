from z3 import *
import itertools
from Data.precis_feature import PrecisFeature
from Learners.sygus import Sygus
from os import sys, path
from Data.shell import Shell
from Learners.sygus_lia import SygusLIA

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
    
    def __init__(self, binaryExec, tempFolder, syguFileName, baseFeatures):
        assert (baseFeatures != None)
        self.binary = binaryExec
        self.temporaryFolder = tempFolder
        self.sygusFileName = syguFileName
        self.baseFeatures = baseFeatures

    def updateBaseFeatureVector(self, baseFv):
        self.baseFeatureVectors = baseFv

    def updateBaseFeatures(self, features):
        self.baseFeatures = features

    def GenerateDerivedFeatures(self):
        intFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Int"]
        boolFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Bool"]
        negationBaseBoolFeatures =()
        equalityFeatures = ()
        #sygusLearner = SygusLIA("esolver", "learner/EnumerativeSolver/bin/starexec_run_Default", "grammar=True", "tempLocation")
        #minus = precisFeature.oldcount - IntVal(1)
        #equal = precisFeature.New  
        #sygusPrecisFeature = PrecisFeature(sygusResult, )
        assert(len(intFeatures) > 0)
        #assert(len(boolFeatures) > 0)
        equalityFeatures: Tuple[PrecisFeature] = self.CreateEqualities(intFeatures)
        
        if len(boolFeatures) > 0: # there exist any base bool observer methods
            negationBaseBoolFeatures: Tuple[PrecisFeature] = self.createNegationBool(boolFeatures)
        
        return negationBaseBoolFeatures + equalityFeatures
        #return equalityFeatures
        #Todo: call to sygus solvers can be placed here.
    def synthesizeFeatures(self):
        assert( self.baseFeatureVectors != None)
        intFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Int"]
        boolFeatures = [f for f in self.baseFeatures if str(f.varZ3.sort())=="Bool"]
        grammar = ""
        assert(len(intFeatures) > 0)

        sygusSynthesizer = SygusLIA(self.binary)
        #grammar = sygusSynthesizer.formatGrammar(sygusSynthesizer.constructGrammar(intFeatures, boolFeatures))
        
        #getting old vars
        intOldVarAndIdxs = [(intFeatures[idx],idx) for idx in range(len(intFeatures)) if intFeatures[idx].isNew != None and not(intFeatures[idx].isNew)]
        intOldVarFeatures = list((map(lambda x:  x[0] , intOldVarAndIdxs)))
        #print(sygusSynthesizer.formatGrammar(grammar))
        
        shell = Shell(True)

        ## wrap this code with a synthesize function
        ## there can be synthesized features that we already add
        logic = [["(set-logic LIA)"]]
        checkSynth = [["(check-synth)"]]
        synthesizedFeatures = ()
        for postFeaturesIdxs  in [ (intFeatures[newIdx], newIdx) for newIdx in range(len(intFeatures)) if intFeatures[newIdx].isNew != None and intFeatures[newIdx].isNew]:
            #print(postFeaturesIdxs[0].varName)
            shell.removeSygusFile(self.temporaryFolder, self.sygusFileEndingPattern)
            
            grammar = sygusSynthesizer.constructGrammar(intOldVarFeatures, boolFeatures)
            constraints = sygusSynthesizer.addSemanticConstraints(postFeaturesIdxs[1],intOldVarAndIdxs, self.baseFeatureVectors)
            sygusProblem = sygusSynthesizer.constructSygusProblem(logic, grammar, constraints,checkSynth)
            shell.writeToFile(self.temporaryFolder,self.sygusFileName, sygusProblem )
            synthizedExprStr = sygusSynthesizer.learn(self.temporaryFolder,self.sygusFileName)
            if synthizedExprStr == "No Solutions!":
                continue
            declMap = { f.varName : f.varZ3 for f in intFeatures}
            synthesizedFeature = "(= "+ postFeaturesIdxs[0].varName +" " +synthizedExprStr +")" 
            sygusExpr = parse_smt2_string("(assert "+ synthesizedFeature+ " )",decls=declMap)
            synthesizedFeatures += (PrecisFeature(True, str(sygusExpr[0]), str(sygusExpr[0].sort()), None, sygusExpr[0]),)
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

    # this method assumes it called with integer features
    def CreateEqualities(self, intFeatures):
        equalitiesFeatures = ()        
        
        if len(intFeatures) <= 1:
            return intFeatures # throw new error
        
        allCombinations = itertools.combinations(intFeatures,2)
        
        for (feat1,feat2) in allCombinations:
            #print (feat1, feat2)
            notEqualExpr = feat1.varZ3 != feat2.varZ3
            equalExpr = feat1.varZ3 == feat2.varZ3
            #print(notEqualExpr)
            #print(notEqualExpr.sort())
            #print(type(notEqualExpr))
            notEqualDerived = PrecisFeature(True, str(notEqualExpr), str(notEqualExpr.sort()), None, notEqualExpr)
            equalDerived = PrecisFeature(True, str(equalExpr), str(equalExpr.sort()), None, equalExpr)
            equalitiesFeatures += (notEqualDerived,)
            equalitiesFeatures += (equalDerived,)
        return equalitiesFeatures
    