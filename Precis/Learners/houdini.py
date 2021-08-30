from z3 import *
import itertools
from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from feature_synthesis import FeatureSynthesis
from sygus2 import Nd
import logging


logger1 = logging.getLogger("Results.DisjunctiveLearner.Houdini")
class Houdini:
    
    useBounds = False

    def __init__(self,intBaseFeatures, boolBaseFeatures, intBaseFeatVectors, boolBaseFeatVectors, derivFeats, synthesizer):
        self.intBaseFeat = intBaseFeatures
        self.boolBaseFeat = boolBaseFeatures
        self.intBaseFvs = intBaseFeatVectors
        self.boolBaseFvs = boolBaseFeatVectors
        self.derivBoolFeats = derivFeats
        self.predicateSynthesizer = synthesizer
        self.predSynthTime = 0

    def learn(self,features,featureVectors,call):
        assert(len(featureVectors) > 0)
        
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        #workList = list(features)
        #oldCount = len(workList)
        for idx in range(0, len(features)):
            #fv is of type feature vector
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if str(fv[idx]) == "False":
                   workList[idx]  = False
                   break 
        conjuncts = []
        
        for idx in range(0, len(features)):
            if workList[idx]:
                conjuncts.append(features[idx].varZ3)
        
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            assert(False) #remove this assertion the first time it is tested
            return PrecisFormula(BoolVal(True))
        
        phi = ""
        houdini = None
        phi = And(conjuncts)
        houdini = PrecisFormula(phi)
        return houdini
    
    def learn2(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            if "implication check" in call:
                return (PrecisFormula(BoolVal(False)),[])
            return (PrecisFormula(BoolVal(True)),[])
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        #workList = list(features)
        #oldCount = len(workList)
        for idx in range(0, len(features)):
            
            #fv is of type feature vector
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if str(fv[idx]) == "False":
                   workList[idx]  = False
                   break 
        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                conjuncts.append(features[idx].varZ3)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[])
        
        phi = ""
        houdini = None
        phi = And(conjuncts)
        houdini = PrecisFormula(phi)
        return (houdini,indexes)
    
    
    def learn4(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            return (PrecisFormula(BoolVal(False)),[],[])
            
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        
        indicesToNegate = {idx: False for idx in range(0, len(features))}
        for idx in range(0, len(features)):
            #fv is of type feature vector
            initVal = featureVectors[0][idx]
            keep = True 
            for fv in featureVectors:
                assert(len(fv) == len(features) )
                if is_true(simplify(fv[idx] != initVal)):
                   workList[idx]  = False
                   keep = False
            if keep and is_false(initVal):
                indicesToNegate[idx] = True
                

        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                validFeature = features[idx]
                if indicesToNegate[idx]:
                    #sort here should be BOOL
                    z3NegatedFeature = Not(validFeature.varZ3)
                    negatedPrecisFeature = PrecisFeature(True, str(z3NegatedFeature), str(z3NegatedFeature.sort()), None, z3NegatedFeature)
                    validFeature = negatedPrecisFeature
                conjuncts.append(validFeature)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[],[])
        
        phi = ""
        houdini = None
        phi = And([c.varZ3 for c in conjuncts])
        houdini = PrecisFormula(phi)
        return (houdini,indexes,conjuncts)
    
    def learnHoudiniString(self, strFeatures, strFeatureVectors):
        workList = {key: True for key in range(0, len(strFeatures))}

        indicesToNegate = {idx: False for idx in range(0, len(strFeatures))}
        for idx in range(0, len(strFeatures)):
            initVal = strFeatureVectors[0][idx]
            keep = True
            for fv in strFeatureVectors:
                # -2 to account for the labeling
                assert(len(fv) == len(strFeatures) )
                if fv[idx] != initVal:
                   workList[idx]  = False
                   keep = False
            #no need to negate because we assume  strFeatures is just literals.
            if keep and (initVal == "false"):
                indicesToNegate[idx] = True
        
        terms = []
        indexes = []
        for idx in range(0, len(strFeatures)):
            if workList[idx]:
                if indicesToNegate[idx]:
                    terms.append("(not "+strFeatures[idx]+")")
                else:
                    terms.append(strFeatures[idx])
                indexes.append(idx)
        
        return (terms, indexes)

    def learn5(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            return (PrecisFormula(BoolVal(False)),[],[])
            
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        
        indicesToNegate = {idx: False for idx in range(0, len(features))}
        for idx in range(0, len(features)):
            #fv is of type feature vector
            initVal = featureVectors[0][idx]
            keep = True 
            for fv in featureVectors:
                if is_true(simplify(fv[idx] != initVal)):
                   workList[idx]  = False
                   keep = False
            if keep and is_false(initVal):
                indicesToNegate[idx] = True
                

        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                validFeature = features[idx]
                if indicesToNegate[idx]:
                    #sort here should be BOOL
                    z3NegatedFeature = Not(validFeature.varZ3)
                    negatedPrecisFeature = PrecisFeature(True, str(z3NegatedFeature), str(z3NegatedFeature.sort()), None, z3NegatedFeature)
                    negatedPrecisFeature.atom = "(not "+ validFeature.atom +")"
                    validFeature = negatedPrecisFeature
                    #if validFeature in self.derivBoolFeats:
                    #    continue
                conjuncts.append(validFeature)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[],[])
        
        phi = ""
        houdini = None
        phi = And([c.varZ3 for c in conjuncts])
        houdini = PrecisFormula(phi)
        return (houdini,indexes,conjuncts)

######################################################################################################
#### NO Negation

    def learn6(self,features,featureVectors, call):
        #assert(len(featureVectors) > 0)
        if len(featureVectors) == 0:
            logger1.info(call+ ": houdini Called with 0 feature vectors")
            print(call +": houdini Called with 0 feature vectors")
            return (PrecisFormula(BoolVal(False)),[],[])
            
        #check datapoint are boolean --> currently assention doesnt work
        #assert(len(featureVectors) or all ( all( v == "True" or v == "False" for v in dp) for dp in featureVectors))
    
        # dict from  index of features to
        workList = {idx: True for idx in range(0, len(features))}
        
        for idx in range(0, len(features)):
            #fv is of type feature vector
            initVal = featureVectors[0][idx]
            for fv in featureVectors:
                if is_false(fv[idx]):
                   workList[idx]  = False
                

        conjuncts = []
        indexes = []
        for idx in range(0, len(features)):
            if workList[idx]:
                validFeature = features[idx]
                conjuncts.append(validFeature)
                indexes.append(idx)
        # early return if no predicates are always true -> houdini should return true
        if len(conjuncts) == 0:
            logger1.info(call+ ": not expressive in with conjunctions")
            print(call +": not expressive in with conjunctions")
            #assert(False) #remove this assertion the first time it is tested
            return (PrecisFormula(BoolVal(True)),[],[])
        
        phi = ""
        houdini = None
        phi = And([c.varZ3 for c in conjuncts])
        houdini = PrecisFormula(phi)
        return (houdini,indexes,conjuncts)



    def synthTighestAtK(self):
        return "true"
    
    def houdiniSynthesis(self, tree, boolFeats, boolFvs, call):
        if len(boolFvs) == 0:
            # Todo: add PrecisFormula.False member in PrecisFormulaClass
            return "false", PrecisFormula(BoolVal(False)), ()
        
        precisConjunction, indices, conjuncts = self.learn5(boolFeats, boolFvs, call)
        commonSMTConjunct = 'true' if len(conjuncts) == 0 else '(and ' + ' '.join([c.atom for c in conjuncts] ) + ')'
        
        print(f"Predicate chosen at  {call}  :  {tree.data}")
        logger1.info(f"Predicate chosen at  {call}  :  {tree.data}")
        if not tree.left and not tree.right:
            synthFeats = tuple()
            uniqueFeats = tuple()
            timeSpent = 0.0
            print("####################### Feature Vector Count: "+ str(len(boolFvs)))
            if len(boolFvs) >= 1:
                fvIds = [bfv.ID for bfv in boolFvs]
                
                relevantIntFvs = [ iFv  for iFv in self.intBaseFvs if iFv.ID in fvIds ]
                #Shambo: remove synthesis call here for RQ4b. Perhaps this whole if case can go away.   
                synthFeats, timeSpent = self.predicateSynthesizer.synthesizeFeatures(self.intBaseFeat, self.boolBaseFeat, relevantIntFvs)

                uniqueFeats = tuple([ f for f in synthFeats if f not in self.derivBoolFeats]) 

            if len(uniqueFeats) > 0:
                commonSMTConjunctSynth = "(and "+commonSMTConjunct +" "+ ' '.join([c.atom for c in uniqueFeats] )+")" 
                #precisConjunctionSynth = PrecisFormula(And(precisConjunction.formulaZ3, And([c.varZ3 for c in uniqueFeats])))
                precisConjunctionSynth = PrecisFormula(And(uniqueFeats[0].varZ3,precisConjunction.formulaZ3  ))# assuming only one feature
                #typically only one is synthesized
                print(f"Adding Unique synthesized feature: {uniqueFeats[0].varName}\n" )
                logger1.info(f"Adding Unique synthesized feature: {uniqueFeats[0].varName}\n" )
                return commonSMTConjunctSynth, precisConjunctionSynth, uniqueFeats, timeSpent

            return commonSMTConjunct, precisConjunction, () ,  timeSpent
        else:
            
            indices.reverse()
            
            condBoolFeats = Houdini.removeCommonTerms(boolFeats, indices)
            condboolFvs = Houdini.removeCommonFvs(boolFvs, indices)
            
            idx = condBoolFeats.index(tree.data) if tree.data in condBoolFeats else -1
            if idx == -1:
                return commonSMTConjunct, precisConjunction, (), 0.0

            splitPred = tree.data
            print(f"Predicate chosen at {call}: {splitPred}")
            logger1.info(f"Predicate chosen at {call}: {splitPred}")

            (posFv, negFv) = Houdini.split(idx, condboolFvs)
            remainingBoolFeats = Houdini.removeCommonTerms(condBoolFeats, [idx])
            remPosFv = Houdini.removeCommonFvs(posFv, [idx])
            remNegFv = Houdini.removeCommonFvs(negFv, [idx])

            rightSmt, rightPrecis, posFeatSynth, rightPredSynthTimeSpent = self.houdiniSynthesis(tree.right, remainingBoolFeats, remPosFv, call+" right")
            leftSmt, leftPrecis, negFeatSynth, leftPredSynthTimeSpent = self.houdiniSynthesis(tree.left, remainingBoolFeats, remNegFv, call+" left")

            smtPost = "(and "+ commonSMTConjunct +" "+ "(ite "+ tree.data.atom + " " + rightSmt + " "+ leftSmt+" "+"))"
            #And(Or(Not(splitPred.varZ3), right ), Or(splitPred.varZ3, left )) )
            precisPost = PrecisFormula(And(precisConjunction.formulaZ3, And(Or(Not(splitPred.varZ3), rightPrecis.formulaZ3) , Or(splitPred.varZ3, leftPrecis.formulaZ3))))
        return smtPost, precisPost, tuple(set(posFeatSynth).union(set(negFeatSynth))), (rightPredSynthTimeSpent + leftPredSynthTimeSpent)
    
    @staticmethod
    def removeCommonFvs(boolFvs, reversedIndexes):
        updateBoolFvs = []
        for vecIdx in range(0, len(boolFvs)):
            changedBoolFv = None
            if len(reversedIndexes) > 0:
                changedBoolFv  = FeatureVector.copyFeatureVector(boolFvs[vecIdx])
                for idx in reversedIndexes:
                    changedBoolFv.values = changedBoolFv.values[0:idx] + changedBoolFv.values[idx+1:]
                    changedBoolFv.valuesZ3 = changedBoolFv.valuesZ3[0:idx] + changedBoolFv.valuesZ3[idx+1:]
                    changedBoolFv.ID = boolFvs[vecIdx].ID
                updateBoolFvs.append(changedBoolFv)
                
            else:
                updateBoolFvs.append(boolFvs[vecIdx])
                
        
        return updateBoolFvs

    @staticmethod
    #atoms can be a list of any type(i.e string, Z3expr) 
    def removeCommonTerms(atoms, reversedIndexes):
         # in place reverse
        updatedAtoms = tuple(atoms)
        for idx in reversedIndexes:
            updatedAtoms = updatedAtoms[0:idx] + updatedAtoms[idx+1: ]
            #atoms[]
        return updatedAtoms

    @staticmethod
    def split(predIndex, boolFvs):
        listPos =[]
        listNeg= []
        #index = Nd.getIndex(predicate)
        for vector in boolFvs:
            # to handle str typed feature vector := str(vector[predIndex]).lower()
            if is_false(vector[predIndex]):
                listNeg.append(vector)
            elif is_true(vector[predIndex]):
                listPos.append(vector)
        return (listPos, listNeg)

    def parseWithHoudiniWithZ3Expr(self, atoms, boolFeatures, boolStrFvs, boolFvs, s, call):
        if len(boolFvs) == 0:
            return  PrecisFormula(BoolVal(False))
        if not self.left and not self.right:
            #Houdini
            houdini = Houdini()
            #houdini should return tuples
            (conjunct, indexes, leafConjunctsZ3expr) = houdini.learn4(boolFeatures, boolFvs, call)
            if len(leafConjunctsZ3expr) == 0:
                infixConjunct = PrecisFormula(BoolVal(True))    
            else:
                infixConjunct = PrecisFormula(And([ pf.varZ3  for pf in leafConjunctsZ3expr ] ))
            
            return infixConjunct            
        else:
            #left is false branch
            #right is true branch
            #(ite  x>=1 (ite  eq2 * * ) * ) ---> (x>1 => ((eq2 =>  ) and (!eq2 => )) ) and (!x>1 => *) 
            #ret = " ".join(["(ite ", self.data ,self.right.parse(),  self.left.parse() , ")"])
            #( (x>=1 => ((eq2 => *) && ( !(eq2) => *))) && ( !(x>=1) => *))
            #(pPos, pNeg) = split(self,data, boolFvs)
            
            houdini2 = Houdini()
            commonConjuct , idxsAtoms = houdini2.learnHoudiniString(atoms, boolStrFvs)
            commonConjuctPrecisFeat , idxsExpr, commonConjunctsZ3expr = houdini2.learn4(boolFeatures, boolFvs, call)
            idxsAtoms.reverse()
            idxsExpr.reverse()
            remainingAtoms = Nd.removeCommonTerms(atoms, idxsAtoms)
            remainingAtomsPrecisFeat = Nd.removeCommonTerms(boolFeatures, idxsExpr)
            remainingAtomsStrBoolFv = Nd.removeCommonStrFvs(boolStrFvs, idxsAtoms)
            remainingBoolFvs = Nd.removeCommonFvs(boolFvs,idxsExpr)
            
            #s.add(And( [f.varZ3 for f in commonConjuctPrecisFeat] if len(commonConjuct) > 0 else [BoolVal(True),BoolVal(True)] ) == BoolVal(True))
            #s.push()

            idx = remainingAtoms.index(self.data) if self.data in remainingAtoms else -1
            if idx == -1: # case where the predicate chosen to split is actually a common term meaning that it will all fvs to one side leaving the other empty
                assert( (atoms.index(self.data) if self.data in atoms else -1) != -1)
                if len(commonConjunctsZ3expr) != 0:
                    earlyRet =  PrecisFormula(And([f for f in commonConjunctsZ3expr]))
                else:
                    earlyRet = PrecisFormula(BoolVal(True))
                print("Predicate: "+ call + " : None")
                logger1.info("Predicate "+ call + " : None"+"\n")
                return earlyRet
            (pStrPos, pStrNeg) = Nd.split(idx,remainingAtomsStrBoolFv) 
            (pPos, pNeg) = Nd.split(idx,remainingBoolFvs)
            splitPred = remainingAtomsPrecisFeat[idx] # chosen predicate to split on LOG THIS
            
            remainingAtomsPrecisFeat = Nd.removeCommonTerms(remainingAtomsPrecisFeat, [idx])
            remainingAtoms = Nd.removeCommonTerms(remainingAtoms, [idx])
            
            pStrPos = Nd.removeCommonStrFvs(pStrPos, [idx])
            pStrNeg = Nd.removeCommonStrFvs(pStrNeg, [idx])
            pPos = Nd.removeCommonFvs(pPos,[idx])
            pNeg = Nd.removeCommonFvs(pNeg,[idx])

            logger.info("Predicate "+ call + " : "+ str(splitPred)+"\n")
            print("Predicate chosen at " + call +" : "+str(splitPred))

            right = self.right.parseWithHoudiniWithZ3Expr(remainingAtoms,remainingAtomsPrecisFeat, pStrPos,  pPos, s, call + " Right").formulaZ3


            left = self.left.parseWithHoudiniWithZ3Expr(remainingAtoms,remainingAtomsPrecisFeat , pStrNeg,  pNeg, s, call + " Left").formulaZ3
            #s.pop() 
            if len(commonConjunctsZ3expr) != 0:
                
                #ret = PrecisFormula( And( And([f.varZ3 for f in commonConjuctPrecisFeat]), Or( Not(splitPred.varZ3), self.right.parseWithHoudiniWithZ3Expr(remainingAtoms,remainingAtomsPrecisFeat, pPos).varZ3), Or(splitPred.varZ3, self.left.parseWithHoudiniWithZ3Expr(remainingAtoms,remainingAtomsPrecisFeat pNeg) ) ))
                ret = PrecisFormula( And(And( [f.varZ3 for f in commonConjunctsZ3expr]), And(Or(Not(splitPred.varZ3), right ), Or(splitPred.varZ3, left )) ))
                
            else:
                #ret = "( (!(" + self.data + ") || " + self.right.parseWithHoudini(remainingAtoms, pPos) \
                #     + ") && ( " + self.data + " || " + self.left.parseWithHoudini(remainingAtoms, pNeg) + "))"
                ret = PrecisFormula(And( Or(Not(splitPred.varZ3), right),\
                    Or(splitPred.varZ3, left )))

            #ret = PrecisFormula(ret.precisSimplify())
            return ret
