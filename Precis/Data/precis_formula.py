from z3 import *
import re

class PrecisFormula:
    
    # formulaZ3: Z3ExprRef; variable of Z3 version ---> more precisely should be BoolRef
    formulaZ3 = None
    # formula is string representation of formula
    formula = ""
    # string rep of formula

    def __init__(self, varZ3):
        self.formulaZ3 = varZ3
        # Z3eprx in string format add a newline after every conjunct
        self.formula = str(varZ3).replace("\n","")

    def toInfix(self):
        s = self.formula
        while True:
            s, flag = self.replace(s)
            if not flag:
                #replace("&&    ","&& ") is to deal with spacing added in z3 expr when toString
                return s.replace("`","(").replace("~",")").replace("&&    ","&& ")
   
    # Acknowledgement: Neil Zhao
    def replace(self, s):
        pattern = re.compile(r'((And|Or)(\(([^,()]+(,[^,()]+))*\)))')
        res = pattern.findall(s)
        for r in res:
            if r[1] == 'And':
                replacement = r[2][1:-1].replace(', ', ' && ')
            else:
                replacement = r[2][1:-1].replace(', ', ' || ')
            s = s.replace(r[0], '`{}~'.format(replacement))
        return s, len(res) > 0
