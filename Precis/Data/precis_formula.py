from z3 import *


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

    #def toInfix