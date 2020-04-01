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
        self.formula = str(varZ3).replace("\n", "")

    # returns string
    def toInfix(self):
        s = self.formula
        while True:
            s, flag = self.replace(s)
            if not flag:
                # replace("&&    ","&& ") is to deal with spacing added in z3 expr when toString
                # symbols ~ and ) are used placed holders for left and right parenthesis.
                # We need these place holders because our regex looks for left and right paren
                replacePlacedHolderFormula = s.replace("`", "(").replace("~", ")") \
                    .replace("&&               ", "&& ").replace("&&           ", "&& ") \
                    .replace("&&        ", "&& ") \
                    .replace("&&       ", "&& ") \
                    .replace("&&     ", "&& ").replace("&&    ", "&& ") \
                    .replace("||                  ", "|| ").replace("||              ", "|| ") \
                    .replace("||            ", "|| ").replace("||       ", "|| ").replace("||   ", "|| ")\
                        .replace("==                          ","== ")\
                            .replace("!=                          ","!= ")

                cSharpCompatibleFormula = replacePlacedHolderFormula.replace(
                    "False", "false").replace("True", "true")
                return cSharpCompatibleFormula

    # Acknowledgement: Neil Zhao
    def replace(self, s):
        pattern = re.compile(r'((And|Or|Not)(\(([^,()]+(,[^,()]+)*)\)))')
        res = pattern.findall(s)
        for r in res:
            if r[1] == 'And':
                conjunct = r[2][1:-1]
                replacement = conjunct.replace(', ', ' && ')
                s = s.replace(r[0], '`{}~'.format(replacement))
            elif r[1] == 'Or':
                disjunct = r[2][1:-1]
                replacement = disjunct.replace(', ', ' || ')
                s = s.replace(r[0], '`{}~'.format(replacement))
            elif r[1] == 'Not':
                negation = r[2][1:-1]
                replacement = negation.replace(', ', ' && ')
                s = s.replace(r[0], '`!`{}~~'.format(negation))
            else:
                assert(False)  # why this case

        return s, len(res) > 0

    def precisAnd(self, other):
        # check other is of type z3eprx
        return PrecisFormula(And(self.formulaZ3. other))

    def precisOr(self, other):
        # check other is of type z3eprx
        return PrecisFormula(Or(self.formulaZ3. other))

    def precisSimplify(self):
        postcondition = self.formulaZ3
        
        set_option(max_args = 10000000, max_lines = 1000000, max_depth = 10000000, max_visited = 1000000)
        set_option(html_mode=False)
        set_fpa_pretty(flag=False)

        #intVars = [ Int(var) for var in intVariables]
        #boolVars = [ Bool(var) for var in boolVariables]

        #declareInts = "\n".join([ "(declare-const " + var + " Int)" for var in intVariables ])
        #declareBools = "\n".join([ "(declare-const " + var + " Bool)" for var in boolVariables ])
        #stringToParse = "\n".join([declareInts,  declareBools, "( assert " + precondition + ")"])

        #logger = logging.getLogger("Framework.z3Simplify")

        # logger.info("############ z3 program")
        # logger.info("############ " + stringToParse)

        #expr = parse_smt2_string(strinagToParse)

        g = Goal()
        g.add(postcondition)
        
        # works = Repeat(Then(
        #     OrElse(Tactic('ctx-solver-simplify'), Tactic('skip')),
        #     OrElse(Tactic('unit-subsume-simplify'),Tactic('skip')),
        #     # OrElse(Tactic('propagate-ineqs'),Tactic('skip')),
        #     # OrElse(Tactic('purify-arith'),Tactic('skip')),
        #       OrElse(Tactic('ctx-simplify'),Tactic('skip')),
        #       OrElse(Tactic('dom-simplify'),Tactic('skip')),
        #     # OrElse(Tactic('propagate-values'),Tactic('skip')),
        #     OrElse(Tactic('simplify'), Tactic('skip')),
        #     #region
        #     # OrElse(Tactic('aig'),Tactic('skip')),
        #     # OrElse(Tactic('degree-shift'),Tactic('skip')),
        #     # OrElse(Tactic('factor'),Tactic('skip')),
        #     # OrElse(Tactic('lia2pb'),Tactic('skip')),
        #     # OrElse(Tactic('recover-01'),Tactic('skip')),
        #     #must to remove ite
        #     # OrElse(Tactic('elim-term-ite'), Tactic('skip')),
        #     # OrElse(Tactic('smt'), Tactic('skip')),
        #     # OrElse(Tactic('injectivity'),Tactic('skip')),
        #     # OrElse(Tactic('snf'),Tactic('skip')),
        #     # OrElse(Tactic('reduce-args'),Tactic('skip')),
        #     # OrElse(Tactic('elim-and'),Tactic('skip')),
        #     # OrElse(Tactic('symmetry-reduce'),Tactic('skip')),
        #     # OrElse(Tactic('macro-finder'),Tactic('skip')),
        #     # OrElse(Tactic('quasi-macros'),Tactic('skip')),
        #     #Repeat(OrElse(Tactic('cofactor-term-ite'), Tactic('skip'))),
        #     Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))),   
        # ))
        
        works = Repeat(Then( 
        #Repeat(OrElse(Tactic('split-clause'),Tactic('skip'))),
                OrElse(Tactic('ctx-solver-simplify'),Tactic('skip')),
                OrElse(Tactic('unit-subsume-simplify'),Tactic('skip')),
                OrElse(Tactic('propagate-ineqs'),Tactic('skip')),
                OrElse(Tactic('purify-arith'),Tactic('skip')),
                OrElse(Tactic('ctx-simplify'),Tactic('skip')),
                OrElse(Tactic('dom-simplify'),Tactic('skip')),
                OrElse(Tactic('propagate-values'),Tactic('skip')),
                OrElse(Tactic('simplify'),Tactic('skip')),
                OrElse(Tactic('aig'),Tactic('skip')),
                OrElse(Tactic('degree-shift'),Tactic('skip')),
                OrElse(Tactic('factor'),Tactic('skip')),
                OrElse(Tactic('lia2pb'),Tactic('skip')),
                OrElse(Tactic('recover-01'),Tactic('skip')),
                OrElse(Tactic('elim-term-ite'),Tactic('skip')), #must to remove ite
                OrElse(Tactic('injectivity'),Tactic('skip')),
                OrElse(Tactic('snf'),Tactic('skip')),
                OrElse(Tactic('reduce-args'),Tactic('skip')),
                OrElse(Tactic('elim-and'),Tactic('skip')),
                OrElse(Tactic('symmetry-reduce'),Tactic('skip')),
                OrElse(Tactic('macro-finder'),Tactic('skip')),
                OrElse(Tactic('quasi-macros'),Tactic('skip')),
                Repeat(OrElse(Tactic('split-clause'),Tactic('skip')))))
        
        result = works(g)
        #result = works1(g)
        # split_all =

        # print str(result)
        # result = [[ "d1", "d2", "d3"], #= conjunct && conjunct
        #           [ "d4", "d5", "d6"]]

        # remove empty subgoals and check if resultant list is empty.
        result = filter(None, result)
        if not result:
            print("there is an error in the custom simplify Z3")
            sys.exit(-9)
        
        # return result
        results = list(result)
        completeConjunct = []
        for i in range(0,len(results)):
            conjunction = results[i]
            completeDisjunct = []
            for literal in conjunction:
                #if i >= 1 and  literal in result[i-1]:
                #    continue
                completeDisjunct.append(literal)

            completeConjunct.append(simplify(And(completeDisjunct)))

        simplifiedPrecondition = Or(completeConjunct)
        return simplifiedPrecondition

        # g1 = Goal()
        # tac = Repeat(Then(
        # OrElse(Tactic('tseitin-cnf'),Tactic('skip')),
        # OrElse(Tactic('cofactor-term-ite'), Tactic('skip')),
        # OrElse(Tactic('ctx-simplify'),Tactic('skip')),
        # OrElse(Tactic('dom-simplify'),Tactic('skip')),
        # OrElse(Tactic('factor'),Tactic('skip')),
        # OrElse(Tactic('elim-term-ite'), Tactic('skip')),
        # ))
        # g1.add(simplifiedPrecondition)
        # post = tac(g1)
        # newConju = And(list(post[0]))
        # print(PrecisFormula(simplify(newConju)).toInfix())
        # print(list(post))
        #print(PrecisFormula(post).toInfix())
        #simplifiedPrecondition = simplifiedPrecondition.replace("Not", " ! ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("False", " false ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("True", " true ")
        #simplifiedPrecondition = simplifiedPrecondition.replace("\n", "  ")
