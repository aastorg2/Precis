import re
import sys
import os
from os import path

print("In sygus2.py: \n" + str(sys.path))

sys.path.append( "..\\" )
from Learners.feature_synthesis import FeatureSynthesis
#from Learners.houdini import Houdini
#from Learners.disjunctive_learner import DisjunctiveLearner

from Learners.command_runner2 import runCommand
#from Learners.houdini import Houdini

from Data.precis_feature import PrecisFeature
from Data.feature_vector import FeatureVector
from Data.precis_formula import PrecisFormula
from z3 import *
import logging



from Data.feature_vector import FeatureVector

distcintConditionals = True


logger = logging.getLogger("Results.Sygus2")

class Nd:
    def __init__(self):
        self.data = None
        self.left = None
        self.right = None
        self.parent = None


    def __str__(self):
        if not self.left and not self.right:
            return "*" 
            # if len(self.data) == 1:
            #     return self.data[0]
            # else: 
            #     return "(and " + ' '.join(self.data) + ")" 
            
        else:
            #left is false branch
            #right is true branch
            #(ite  x>=1 (ite  eq2 * * ) * ) ---> (x>1 => ((eq2 =>  ) and (!eq2 => )) ) and (!x>1 => *) 
            ret = " ".join(["(ite ", str(self.data),str(self.right),  str(self.left), ")"])
            return ret
    """
    def parseWithHoudiniWithPruning (self, condAtoms, condBoolFvs):
        if len(condBoolFvs) == 0:
            return 'false'
        if not self.left and not self.right:
            #Houdini
            houdini = Houdini()
            (conjunct, indexes) = houdini.learnHoudiniString(condAtoms, condBoolFvs)
            infixConjunct = 'true' if len(conjunct) == 0 else '(and ' + ' '.join(conjunct) + ')'   
            return infixConjunct
            # if len(self.data) == 1:
            #     return self.data[0]
            # else: 
            #     return "(and " + ' '.join(self.data) + ")" 
        else:
            #left is false branch
            #right is true branch
            #(ite  x>=1 (ite  eq2 * * ) * ) ---> (x>1 => ((eq2 =>  ) and (!eq2 => )) ) and (!x>1 => *) 
            #ret = " ".join(["(ite ", self.data ,self.right.parse(),  self.left.parse() , ")"])
            #( (x>=1 => ((eq2 => *) && ( !(eq2) => *))) && ( !(x>=1) => *))
            houdini2 = Houdini()
            commonConjuct , idxs = houdini2.learnHoudiniString(condAtoms, condBoolFvs)
            idxs.reverse()
            remainingAtoms = Nd.removeCommonTerms(condAtoms, idxs)
            remainingBoolFvs = Nd.removeCommonStrFvs(condBoolFvs,idxs)
            # inneficient way to check
            idx = remainingAtoms.index(self.data) if self.data in remainingAtoms else -1
            if idx == -1: # case where the predicate chosen to split is actually a common term meaning that it will all fvs to one side leaving the other empty
                assert( (condAtoms.index(self.data) if self.data in condAtoms else -1) != -1)
                earlyRet = 'true' if len(commonConjuct) == 0 else "(and "+ ' '.join(commonConjuct) + ")"
                return earlyRet

            (pPos, pNeg) = Nd.split(idx, remainingBoolFvs)
            #ret =  "((!(" + self.data + ") || " + self.right.parseWithHoudiniWithPruning(condAtoms, pPos) \
            #+ ") && ( " + self.data + " || " + self.left.parseWithHoudiniWithPruning(condAtoms, pNeg) + "))"
            if len(commonConjuct) != 0:
                ret = "(and "+ ' '.join(commonConjuct) +" (ite  " + self.data + " " + self.right.parseWithHoudiniWithPruning(remainingAtoms, pPos) \
                + " " + self.left.parseWithHoudiniWithPruning(remainingAtoms, pNeg) + " )" + " )"
            else: 
                ret = "(ite  " + self.data + " " + self.right.parseWithHoudiniWithPruning(remainingAtoms, pPos) \
                + " " + self.left.parseWithHoudiniWithPruning(remainingAtoms, pNeg) + " )" 
            return ret

    def parseWithHoudini(self, atoms, boolFvs):
        if len(boolFvs) == 0:
            return 'false'
        if not self.left and not self.right:
            #Houdini
            houdini = Houdini()
            (conjunct, indexes) = houdini.learnHoudiniString(atoms, boolFvs)
            if len(conjunct) == 0:
                infixConjunct = 'true'    
            else:
                infixConjunct = '(' + ' && '.join(conjunct) + ')'
            
            return infixConjunct            
        else:
            #left is false branch
            #right is true branch
            #(ite  x>=1 (ite  eq2 * * ) * ) ---> (x>1 => ((eq2 =>  ) and (!eq2 => )) ) and (!x>1 => *) 
            #ret = " ".join(["(ite ", self.data ,self.right.parse(),  self.left.parse() , ")"])
            #( (x>=1 => ((eq2 => *) && ( !(eq2) => *))) && ( !(x>=1) => *))
            #(pPos, pNeg) = split(self,data, boolFvs)
            
            houdini2 = Houdini()
            commonConjuct , idxs = houdini2.learnHoudiniString(atoms, boolFvs)
            idxs.reverse()
            remainingAtoms = Nd.removeCommonTerms(atoms, idxs)
            remainingBoolFvs = Nd.removeCommonStrFvs(boolFvs,idxs)
            idx = remainingAtoms.index(self.data) if self.data in remainingAtoms else -1
            if idx == -1: # case where the predicate chosen to split is actually a common term meaning that it will all fvs to one side leaving the other empty
                assert( (atoms.index(self.data) if self.data in atoms else -1) != -1)
                if len(commonConjuct) != 0:
                    earlyRet = "("+ ' && '.join(commonConjuct) + ")"
                else:
                    earlyRet = 'true'

                return earlyRet
            
            (pPos, pNeg) = Nd.split(idx, remainingBoolFvs)
            
            if len(commonConjuct) != 0:
                ret =  "(("+ ' && '.join(commonConjuct)+ ") && " +"((!(" + self.data + ") || " + self.right.parseWithHoudini(remainingAtoms, pPos) \
                + ") && (" + self.data + " || " + self.left.parseWithHoudini(remainingAtoms, pNeg) + ")))" 
            else:
                ret = "( (!(" + self.data + ") || " + self.right.parseWithHoudini(remainingAtoms, pPos) \
                     + ") && ( " + self.data + " || " + self.left.parseWithHoudini(remainingAtoms, pNeg) + "))"
            
            return ret
    
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
                logger.info("Predicate "+ call + " : None"+"\n")
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
    """

    @staticmethod
    def removeCommonStrFvs(strBoolFvs, reversedIndexes):
        updateBoolFvs = []
        for vecIdx in range(0, len(strBoolFvs)):
            changedBoolFv  = list(strBoolFvs[vecIdx])
            for idx in reversedIndexes:
                changedBoolFv = changedBoolFv[0:idx] + changedBoolFv[idx+1:]
            updateBoolFvs.append(changedBoolFv)
        return updateBoolFvs


    @staticmethod
    def removeCommonFvs(boolFvs, reversedIndexes):
        updateBoolFvs = []
        for vecIdx in range(0, len(boolFvs)):
            changedBoolFv  = FeatureVector.copyFeatureVector(boolFvs[vecIdx])
            for idx in reversedIndexes:
                changedBoolFv.values = changedBoolFv.values[0:idx] + changedBoolFv.values[idx+1:]
                changedBoolFv.valuesZ3 = changedBoolFv.valuesZ3[0:idx] + changedBoolFv.valuesZ3[idx+1:]
            updateBoolFvs.append(changedBoolFv)
        
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

    #@staticmethod
    #def findIndex(p, atom):
    #    re

    @staticmethod
    def split(predIndex, boolFvs):
        listPos =[]
        listNeg= []
        #index = Nd.getIndex(predicate)
        for vector in boolFvs:
            # to handle str typed feature vector := str(vector[predIndex]).lower()
            if is_false(vector[predIndex]) or  str(vector[predIndex]).lower() == "false":
                listNeg.append(vector)
            elif is_true(vector[predIndex]) or str(vector[predIndex]).lower() == "true":
                listPos.append(vector)
        return (listPos, listNeg)
    
    @staticmethod
    def getIndex(string):
        ret = ''.join([i for i in string if i.isdigit()])
        return int(ret)

class Node(Nd):
    def __init__(self):
        super().__init__()
        # self.selectme_history = [] 
        # self.selectme_current = []
        self.selectme = []
        self.k = None
        self.index = None
        self.constraint = None
    

class SygusDisjunctive:

    

    def __init__(self, pred_names, pred_data, rounds, k, cdt="true"):
        #self.cond_pred = pred_names
        #self.cond_pred = [x.replace(" ","aaa") for x in pred_names]
        self.cond_pred = pred_names
        #self.cond_pred  = pred_names
        #print(self.cond_pred)
        self.cond_pred_data = pred_data
        

        self.atomToPrecisFeat = {precisF.atom: precisF for precisF in self.cond_pred}
        assert(k>0)
        self.k = k
        
        self.cdt = cdt
        self.dp_trees = {}
        self.all_trees = self.generate_all_trees(k)
        logger.info(f"trees at round: {rounds} for k = {k}\n")
        logger.info(f"number of boolean variables {len(pred_names)}\n")
        logger.info(f"number of datapoints {len(pred_data)}\n")
        logger.info(f"number of trees generated for {len(self.all_trees)}\n")
        logger.info(f"trees\n")
        for tree in self.all_trees:
            logger.info(f"{tree}\n")

        self.pvariables = {}
        for k_itr in range(self.k):
            self.pvariables[k_itr] = []
            for p_itr in self.cond_pred:
                self.pvariables[k_itr].append('p_'+str(k_itr) + '_' + p_itr.atom)
                
        self.wvariables = [] 
        self.uvariables = []
        
        for pred  in self.cond_pred: 
            self.wvariables.append('w_'+pred.atom)
            self.uvariables.append('u_'+pred.atom)
        
        self.p_count=0
        self.q_count=0  
        

    
    def generate_all_trees(self, k):
        
        if k in self.dp_trees:
            return self.dp_trees[k]
        
        if k == 0 :
            self.dp_trees[k] = [[""]]
        # elif k == 1:
        #     self.dp_trees[k] = [["0", "1"]]
        
        else: 
            trees = []
            for i in range(0, k):
                for trl in self.append_tree("0",self.generate_all_trees(i)):
                    for trr in self.append_tree("1", self.generate_all_trees(k-1-i)):
                        combined = sorted(trl + trr, key=lambda x: (len(x),x))
                        trees.append(combined)
            
            self.dp_trees[k] = trees #sorted(trees, key=lambda x: (len(x),x))
            
        return self.dp_trees[k]
        
    def append_tree(self, prefix, list_trees):
        res = []
        for tree in list_trees:
            tr = list(map(lambda y: prefix+y, tree))
            res.append(tr)
        return res
    
    
    def zip_column(self, *argv):  
        result = [] 
        
        length = 1
        for arg in argv:  
            if isinstance(arg, list):
                if length == 1:
                    length = len(arg)
                else: 
                    assert( len(arg) == length)
        
        for itr in range(length):
            row = ""
            for arg in argv: 
                if isinstance(arg, str):
                    row+= " " + arg + " "
                elif isinstance(arg, int):
                    row+= " " + str(arg) + " "  
                elif isinstance(arg, list):
                    if isinstance(arg[itr], str):
                        row += " " + arg[itr] + " "
                    elif isinstance(arg[itr], int):
                        row += " " + str(arg[itr]) + " "
                    elif isinstance(arg[itr], list):
                        for element in arg[itr]:
                            if isinstance(element, str):
                                row+= " " + element + " "
                            elif isinstance(element, int):
                                row += " " + str(element) + " " 
                    
                    # row += 
                    # row += ''.join(list(map(lambda x: str(x) if isinstance(x,int) else x, arg[itr])))
            
            result.append(row)
        return result
    
    
    
    def set_logic(self, logic ="BV"):
        return "( set-logic " + logic + " )\n"
    
    def synth_conditionals(self):
        ret = ''
        for k, value in self.pvariables.items():
            ret += '\n'.join(self.zip_column('(synth-fun ', value, '() Bool )' )) + '\n'
        return ret
    
    def synth_witness(self):
        return '\n'.join(self.zip_column( '(synth-fun ', self.wvariables, ' () Bool)' ))
    
    def declare_universal_variables(self):
        return '\n'.join(self.zip_column( '(declare-var ', self.uvariables,  ' Bool)'))
    
    def define_CDT(self):
        ret = "(define-fun cdt (" 
        ret +=  ' '.join([ "( " + x.atom + " Bool)" for x in self.cond_pred])
        ret += ") Bool \n " + self.cdt + "\n)\n"  
        return ret
    
    def generate_constraint(self):
        ret = "(constraint \n(and\n"
                
        for k_itr in range(self.k):
            ret += "(or " + ' '.join(self.pvariables[k_itr]) + ")\n"
            for p_itr in range(len(self.pvariables[k_itr])):
                    ret += "(=> " + self.pvariables[k_itr][p_itr] + " (and "
                    ret += ' '.join(list(map(lambda x: "( not " + x + ")", self.pvariables[k_itr][0:p_itr] + self.pvariables[k_itr][p_itr+1:]))) 
                    ret += "))\n"
            
        ret += '( => ( eval ' + ' '.join(self.uvariables) + ' ' \
                              + ") (cdt " + ' '.join(self.uvariables) + "))\n"
                              
        ret += "(cdt " + ' '.join(self.wvariables) + ")\n"
        ret += "(not (eval " + " ".join(self.wvariables) + " ))\n"
        
        
        if distcintConditionals:
            # add constraint if a predicate is chosen no other node can have that predicate
            # p_i_c => and (not p_j_c) 
            if self.k > 1:
                for p_itr in range(len(self.cond_pred)):
                    for i in range(self.k):
                        ret += "(=>  p_" + str(i) + "_" + self.cond_pred[p_itr].atom + " (and true "
                        for j in range(self.k):
                            if i == j:
                                continue
                            ret += " (not p_" + str(j) + "_" + self.cond_pred[p_itr].atom + " )" 
                        ret += ") )\n"
        
        
        ret += "))"
        return ret
    
    def generate_selectme_fn(self):
        ret = "(define-fun selectme (" 
        ret += ' '.join( ["( value_" + str(i) + " Bool)" for i in range(len(self.cond_pred))] #leafnodes
                        +["( p_i_" + str(i) + " Bool)" for i in range(len(self.cond_pred)) ]) #cond_predicates
        ret += ") Bool\n"
        
        ending = "" 
        for i in range(len(self.cond_pred)):
            ret+= "(ite  p_i_" + str(i) + " value_" + str(i) + "\n"
            ending += ")"
    
        ret += "false " + ending + "\n)\n"
        return ret
    
    def generate_static_file(self):
        return  str(
                    self.set_logic() + "\n"
                    + self.synth_conditionals() + "\n"
                    + self.synth_witness() + "\n"
                    + self.define_CDT() + "\n"
                    + self.declare_universal_variables() + "\n"
                    + self.generate_selectme_fn() + "\n"
                )
    
    
    
    def selectme_statement(self, k):
        selectme_list = []
        for s_i in range(len(self.cond_pred_data)):
            ret = " (selectme "
            end = "" 
            for p_itr in range(len(self.cond_pred)):
                    ret += " " + str(self.cond_pred_data[s_i][p_itr]).lower() + " "
                    end += " p_"+ str(k) + "_" + self.cond_pred[p_itr].atom + " "
            ret += end + ") "
            selectme_list.append(ret)

        return selectme_list
    
    
    def insert_leaf(self, root, index): 
        root_itr = root
        for dir in index: 
            if dir == "0":
                if not root_itr.left:
                    root_itr.left = Node() 
                root_itr = root_itr.left
            if dir == "1":
                if not root_itr.right:
                    root_itr.right = Node() 
                root_itr = root_itr.right
        root_itr.index = index
        return
    
    
    def label_tree(self, root):
        if not root.selectme:
            root.selectme = [ "" for i in range(len(self.cond_pred_data))] 
        
        if not root.left and not root.right:
            root.k = self.q_count
            self.q_count += 1
            
            ret = "(and \n"
            for cond_itr in range(len(self.cond_pred)):
                ret += "(=> (not " + self.cond_pred[cond_itr].atom + " )\n(or\n"
                ret += '\n'.join(self.zip_column('(and', root.selectme, 
                                    '(not ' ,  [ str(x[cond_itr]).lower() for x in self.cond_pred_data],  '))' ))
                ret += "\n)\n)\n"
            ret += ")\n"
            
            root.constraint = ret
        
        
        
        else:
            root.k = self.p_count
            self.p_count += 1
            
            current_selectme = self.selectme_statement(root.k)
            
            root.left.selectme = self.zip_column(root.selectme, "(not ", current_selectme, ")")
            root.right.selectme = self.zip_column(root.selectme, current_selectme)
            
            root.constraint = "(selectme  " + " ".join([p.atom for p in self.cond_pred]) + " " + " ".join([x  for x in self.pvariables[root.k]]) + " )\n"
             
            self.label_tree(root.left )
            self.label_tree(root.right)
            
        return
    
    
    def tree_to_smt(self, node):
        if not node.left and not node.right:
            return node.constraint
        else:
            #print(node.constraint)
            #print(node.constraint.replace("aaa",""))
            return "(ite\n" + node.constraint + "\n" + self.tree_to_smt(node.right) +  "\n" + self.tree_to_smt(node.left)  + ")\n"
    
    
    
    def generate_eval(self, root):
        ret= str("(define-fun eval (" + ' '.join(["( " + x.atom + " Bool)" for x in self.cond_pred]) 
                                   + ") Bool\n")
        #print("here "+self.tree_to_smt(root).replace("aaa"," "))
        ret += self.tree_to_smt(root) + "\n)\n"
        return ret
    
    
    def run_solver(self, constraint):
        
        with open("sygus.sl", "w") as file:
            file.write(constraint)
        
        #output = runCommand(["./Learners/cvc4.exe", "--sygus-out=sygus-standard",  "--lang=sygus2", "sygus.sl"])
        current = path.dirname(path.abspath(__file__))
        currentCvc4 =current+"\\cvc4.exe"
        print(currentCvc4)
        output = runCommand([currentCvc4, "--sygus-out=sygus-standard",  "--lang=sygus2", "sygus.sl"])
        print("cvc4 output: ")
        print(output)
        if output: 
            if "\r\n" in output: 
                output = re.sub("\'?\\r\\nb\'?", "\n", output)

            valuation = re.findall('\s*\(define\-fun\s+(.*)\s+\(\s*\)\s+Bool\s+(.*)\s*\)', output) 
            #if "(fail)" in output:
            #    return []
            if len(valuation) == 0:
                return None
            else:
                return valuation 
            
        return None
    
    # if not self.left and not self.right:
    #         return "*"
    #         parentnode = self.parent
    #         conjunct = true
    #         while parentnode != None:
    #             conjunct = conjunct && parentnode.data
    #             parentnode = parentnode.parent
            
    #         filteredSamples = filterSamples(conjunct, data)
    #         return houdini(filteredSamples, predicates)
    #         ((x>=1 => ((eq2 => *) && ( !(eq2) => *))) && ( !(x>=1) => *)
    def project_copy(self, root, predicates_chosen, parent = None):
            if not root:
                return None
            
            new_root = Nd()
            
            if not root.left and not root.right:
                new_root.data = "*"
                new_root.parent = parent
                # new_root.data = equalities_chosen[root.k]
                
                
            else:
                new_root.data = predicates_chosen[root.k]
                new_root.left = self.project_copy(root.left, predicates_chosen, new_root)
                new_root.right = self.project_copy(root.right, predicates_chosen, new_root)
                new_root.parent = parent
            return new_root

    # def project_copy(self, root, predicates_chosen):
    #     if not root:
    #         return None
        
    #     new_root = Nd()
        
    #     if not root.left and not root.right:
    #         # this is the leaf case
    #         new_root.data = "*"
    #         new_root.parent = root
    #         # new_root.data = equalities_chosen[root.k]
            
            
    #     else:
    #         new_root.data = predicates_chosen[root.k]
    #         new_root.left = self.project_copy(root.left, predicates_chosen)
            
    #         new_root.right = self.project_copy(root.right, predicates_chosen)

    #     return new_root
    
    
    def run_sygus(self):
        for tree in self.all_trees:
            
            root = Node() 
            for leaf_index in tree:
                self.insert_leaf(root, leaf_index)
            
            self.p_count = 0
            self.q_count=0 
            
            self.label_tree(root)
                        
            constraint = str( self.generate_static_file()  + "\n"
                                    + self.generate_eval(root) +"\n"
                                    + self.generate_constraint() + "\n"
                                    + "(check-synth)")
            # print(constraint)
            soln = self.run_solver(constraint)
            
            if soln == None:
                return None

            #if len(soln) == 0:
                #new_root = Nd()
                #new_root.data = "true"
                #root.data = "true"
                #return new_root

            if soln:
                predicates_chosen = {}
                for i in range(self.k):
                    for element in soln:
                        if 'p_' + str(i) + '_' in element[0] and element[1] == 'true':
                            predicates_chosen[i] = self.atomToPrecisFeat[element[0].replace('p_' + str(i) + '_', '')]
                            break
                
                new_root = self.project_copy(root, predicates_chosen)
                    
                return new_root
                
                # return tree, predicates_chosen
                
                
        
        return None


#def main(): 
if __name__ == '__main__':
    print("here")
    solver1 = SygusDisjunctive(

                    ["cond1", "cond2", "cond3", "cond4", "eq1", "eq2", "eq3"],
                    
                    [["true", "false", "true", "true","true", "false", "true"],
                    ["true", "true", "true", "true","false", "false", "false"]],
                    
                    k=1,
                    cdt="(and cond1 cond3 )"
                )
    print(os.getcwd())
    output_tree = solver1.run_sygus()
    print(output_tree)
    if output_tree != None:
        stringTree = output_tree.parseWithHoudiniWithPruning(["cond1", "cond2", "cond3", "cond4", "eq1", "eq2", "eq3"], [["true", "false", "true", "true","true", "false", "true"],["true", "true", "true", "true","false", "false", "false"]] )
        print(stringTree)
    print("no output")
    #print(stringTree)
    
    # t = "true"
    # f = "false"
    
    # solver2 = SygusDisjunctive(
    #                     ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],

    #                     [[t,t,f,t,t,f],
    #                     [f,t,f,t,t,f],
    #                     [f,f,t,t,f,f],
    #                     [t,f,f,t,f,t]
    #                     ],
                    
    #                     k = 1,
    #                     cdt = "c1" # no soln
    #                     # cdt = "true" # (ite  c2 * * )
    #                  )
    # output_tree = solver2.run_sygus()
    # print(output_tree)
    
    # solver3 = SygusDisjunctive(
    #                     ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],

    #                     [[t,t,f,t,t,f],
    #                     [f,t,f,t,t,f],
    #                     [f,f,t,t,f,f],
    #                     [t,f,f,t,f,t]
    #                     ],
                
    #                     k = 1,
    #                     #  cdt = "c1" # no soln
    #                     cdt = "true" # (ite  c2 * * )
    #                  )
    # output_tree = solver3.run_sygus()
    # print(output_tree)
    
    # solver4 = SygusDisjunctive(
    #                     ['c1', "c2", "c3", "c4", "c5", 'e1', 'e2', 'e3', 'e4', 'e5', 'e6'],
                        
    #                     [[t,f,t,t,t,f,t,f,f,t,t],
    #                      [t,t,f,t,f,f,t,t,f,f,f],
    #                      [t,t,t,f,f,t,t,f,f,f,t]
    #                     ], 
                        
    #                     k = 1,
    #                     cdt = "true"
    # )
    
    # output_tree = solver4.run_sygus()
    # print(output_tree)
    
    
    # solver5 = SygusDisjunctive( 
    #                     ["c1", "c2", "e1", "e2", "e3"],
        
    #                     [[t,f,t,t,f],
    #                      [f,f,t,f,t],
    #                     ],
                        
    #                     k = 1,
    #                     cdt = "true"
    # )
    
    # output_tree = solver5.run_sygus()
    # print(output_tree)


#main()


# p = solver.zip_column(
#     [[1,2,3],[4,5,6]], "(not",   [[9,8,7],[6,5,4]], ")"     
# )
