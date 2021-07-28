from z3 import *
from abc import ABC, abstractmethod
import logging
from _functools import reduce

from Data.precis_feature import PrecisFeature
from Data.shell import Shell
import re
class Sygus:

    #binary executable to run sygus solver
    binary = ""

    def __init__(self, execBin):
        self.binary = execBin
        #super().__init__()

   
    #Todo: handle the case when no boolean feature vectors are given
    @abstractmethod
    def constructGrammar(self, intFeatures, boolFeatures):
        intStr = list((map(lambda x:  str(x) , intFeatures)))
        intDecl = list((map(lambda x: "(" + x + " Int)", intStr)))
        boolStr = list((map(lambda x:  str(x), boolFeatures)))
        boolDecl = list((map(lambda x: "(" + x + " Bool)", boolStr)))
        
        intConsts = ["0", "1"]
        boolConsts = ["true", "false"]
        
        synthFuncDecl = "synth-fun Postcondition"

        startSymbolBool = ["(", "Start",  "Bool",  "(StartBool)", ")"]

        intArithProductions = [["(+ StartInt StartInt)"], ["(- StartInt StartInt)"]] #, ["(ite StartBool StartInt StartInt)"]]
        intCompareProductions = [["(<=  StartInt StartInt)"], ["(= StartInt StartInt)"], ["(>=  StartInt StartInt)"]]
        boolProductions = [["(and StartBool StartBool)"], ["(or StartBool StartBool)"], ["(not StartBool)"]]

        boolGrammar = [ ["(", "StartBool", "Bool", "("],
                        [boolConsts],
                        [boolStr],
                        boolProductions,
                        intCompareProductions,
                        [ ")", ")" ]
        ]

        intGrammar =[  ["(", "StartInt", "Int", "("],
                       [intConsts],
                       [intStr],
                       intArithProductions,
                       [")", ")"]
        ]

        grammar = [  [ "(", synthFuncDecl,"("] +  intDecl + boolDecl + [")", "Bool", "(" ],
                     [startSymbolBool],
                     boolGrammar,
                     intGrammar,
                     [ ")", ")"]
                  ]
        return grammar

    def formatGrammar(self, grammar, tab = 0):
        #is it a non list variable?
        if not isinstance(grammar, list):
            return str(grammar)

        #its a list, now:
        # are all elements of the list non lists??
        areNotList = Sygus.AreAllElemenentNotList(grammar)
        if reduce((lambda x, y: x and y), areNotList , True):
            return  ("\t" * tab + " ".join(map(lambda x: self.formatGrammar(x, tab + 1), grammar)))

        #some element still has arrays
        else:
            return "\n".join(map(lambda x: self.formatGrammar(x, tab + 1), grammar))

    @staticmethod
    def AreAllElemenentNotList(grammar):
        return list(map(lambda x: not isinstance(x, list), grammar))

    #@abstractmethod
    def addSemanticConstraints(self, featureVectors):
        constraints = []
        for fv in featureVectors:
            fnCall =  ["(", "Postcondition"]  +  list(fv[:-1]) + [")"]

            #always positive examples in the postcondition case
            #if fv[-1] == "false":
            #    fnCall = ["(", "not"] + fnCall + [")"]

            constraints.append(["(", "constraint"] + fnCall + [")"])
        return constraints
    
    def constructSygusProblem(self, logic, grammar, constraints, checkSynth):
        
        program = [logic, grammar, constraints, checkSynth]
        programFile = self.formatGrammar(program)
        return programFile

    def learn(self, directory, sygusFileName):
        shell = Shell(True)
        absoluteBin = shell.getAbsolutePathByOs(self.binary, "win")
        #print(absoluteBin)
        path, execBin = os.path.split(absoluteBin)
        #print(path)
        #print(execBin)
        linuxFullPath = shell.getAbsolutePathByOs(directory +"/" +sygusFileName, "wsl")
        #print("fullpath: ", linuxFullPath)
        args = " ".join([Shell.wslBin(), './' + execBin, linuxFullPath])
        #print(args)
        result = shell.runCommand(args, path)
        if result == "No Solutions!":
            return "No Solutions!"
            #return "no solution"
        result = self.readResults(result)
        return result
    
    def readResults(self, result):
        resultRegex = '\(\s*define-fun\s+Postcondition\s*\((?:\(\s*[_0-9A-Za-z]+\s*(?:Int|Bool)\s*\)\s*)*\)\s*(?:Int|Bool)\s+(.*)\)'
        
        regex = re.search(resultRegex, result,  re.MULTILINE | re.DOTALL)
        
        if regex:
            program  = regex.group(1)
            return program
        elif result == '': # when calling solver with zero featureVectors
            print("SHOULD NOT BE HERE!")
            return "0"
            #return "No Solutions!"
        else:
            raise(NameError("couldnot parse sygus output:" +result ))
            # shell.printExceptionAndExit(NameError("couldnot parse sygus output"), "output:" + result)