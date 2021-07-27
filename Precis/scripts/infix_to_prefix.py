import ast
import argparse
import os

class NodeVisitor(ast.NodeVisitor):

    def __init__(self):
        self.tokens = []

    def _clear(self):
        self.tokens = []
    
    def __str__(self):
        return "".join(self.tokens)

    def visit_Add(self, node):
        self.tokens.append("+")
    
    def visit_And(self, node):
        self.tokens.append("and")

    def visit_BinOp(self, node):
        self.tokens.append("(")
        self.visit(node.op)
        self.tokens.append(" ")
        self.visit(node.left)
        self.tokens.append(" ")
        self.visit(node.right)
        self.tokens.append(")")
    
    def visit_BoolOp(self, node):
        self.tokens.append("(")
        self.visit(node.op)
        for value in node.values:
            self.tokens.append(" ")
            self.visit(value)
        self.tokens.append(")")

    def visit_Compare(self, node):
        operator = node.ops[0]
        if operator.__class__.__name__ == "NotEq":
            # Contruct Equal comparison
            eq_comparision = node
            eq_comparision.ops = [ast.Eq()]
            # Construct Not operation
            not_op = ast.UnaryOp()
            not_op.op = ast.Not()
            not_op.operand = eq_comparision
            self.visit_UnaryOp(not_op)
        else:
            self.tokens.append("(")
            self.visit(operator)
            self.tokens.append(" ")
            self.visit(node.left)
            for comparator in node.comparators:
                self.tokens.append(" ")
                self.visit(comparator)
            self.tokens.append(")")

    def visit_Div(self, node):
        self.tokens.append("/")
    
    def visit_Eq(self, node):
        self.tokens.append("=")

    def visit_Gt(self, node):
        self.tokens.append(">")

    def visit_GtE(self, node):
        self.tokens.append(">=")

    def visit_Lt(self, node):
        self.tokens.append("<")

    def visit_LtE(self, node):
        self.tokens.append("<=")

    def visit_Mod(self, node):
        self.tokens.append("mod")

    def visit_Mult(self, node):
        self.tokens.append("*")

    def visit_Name(self, node):
        self.tokens.append(node.id)

    def visit_Num(self, node):
        self.tokens.append(str(node.n))

    def visit_Not(self, node):
        self.tokens.append("not")

    def visit_Or(self, node):
        self.tokens.append("or")

    def visit_Sub(self, node):
        self.tokens.append("-")

    def visit_UnaryOp(self, node):
        operator = node.op
        if operator.__class__.__name__ == "USub":
            new_num = ast.Num()
            new_num.n = -1 * node.operand.n
            node.operand = new_num
            self.visit(node.operand)
        else:
            self.tokens.append("(")
            self.visit(operator)
            self.tokens.append(" ")
            self.visit(node.operand)
            self.tokens.append(")")


# Inserts the prefix formulas into the inspection file
def insert(inspection_file: "str", insertions: "list")->"None":
    abs_path_to_inspection = os.path.abspath(inspection_file)

    inspection = open(abs_path_to_inspection, 'r')
    lines = inspection.readlines()
    inspection.close()

    inspection = open(abs_path_to_inspection, "w")
    for line_index in range(0, len(lines)):
        for insertion in insertions:
            if line_index == insertion[1]:
                lines[line_index] += f"\nCNF simplified (smt): {insertion[0]}\n"
        inspection.write(lines[line_index])
    inspection.close()

# Extracts the CNF formulas from the subject
def get_cnf_formulas(inspection_file: "str")->"list":
    formulas = list()

    abs_path_to_inspection = os.path.abspath(inspection_file)

    inspection = open(abs_path_to_inspection, 'r')
    lines = inspection.readlines()
    inspection.close()

    for line_index in range(0, len(lines)):
        if "CNF simplified:" in lines[line_index]:
            slice_index = lines[line_index].index(":") + 1
            formula = lines[line_index][slice_index:].replace("\n", "").strip()
            formula = convert_operators(formula)
            formulas.append((formula, line_index))

    return formulas


# Converts C# operators into python equivalent
def convert_operators(code: "str")-> "str":
    return code.replace("&&", "and").replace("||", "or").replace("!(", "not(")


#NOTE Hypth: Because We convert to python expression, the order of operations is resolved as 

#  CNF simplified (smt) :=

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--inspection-files","-i", type=str, nargs=argparse.ONE_OR_MORE, required=True)
    args = parser.parse_args()

    inspection_files = args.inspection_files

    for inspection in inspection_files:
        insertions = list()
        cnf_formulas = get_cnf_formulas(inspection)
        visitor = NodeVisitor()
        for formula in cnf_formulas:
            visitor._clear()
            tree = ast.parse(formula[0])
            visitor.visit(tree)
            new_formula = str(visitor)
            insertions.append((new_formula, formula[1]))
    
            #print(f"PREFIX: {visitor}\n\n")

        insert(inspection, insertions)