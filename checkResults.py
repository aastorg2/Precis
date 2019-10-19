import csv
import sys
from typing import List, Type

class Case:
    k = ""
    rounds = ""
    postcondition = ""
    simplifiedPostcondition = ""

    def __init__(self, k: str, rounds: str, postcondition :str, simplifiedPostcondition :str ):
        self.k = k
        self.rounds = rounds
        self.postcondition = postcondition
        self.simplifiedPostcondition = simplifiedPostcondition

    def __str__(self):
        return "case: k == "+self.k + "\n" + "rounds: "+self.rounds +"\n"+"Postcondition:\n"+self.postcondition+"\n"+"Simplified Post:\n"+ self.simplifiedPostcondition

    def __eq__(self, other):
        return self.k == other.k and self.rounds == other.rounds and self.postcondition == other.postcondition and self.simplifiedPostcondition == other.simplifiedPostcondition

    
class PUT:
    putName = ""
    cases = []
    k1 = False
    k2 = False
    onlyk2 = False

    def __init__(self, name: str):
        self.putName = name
    
    def addCase(self, case):
        self.cases.append(case)

    def addCases(self, cases):
        self.cases = cases

    def getCases(self):
        return self.cases
    
    def __str__(self):
        return self.putName+"\nk1 disjunctive: "+str(self.k1)+\
            "\nk2 disjunctive: "+ str(self.k2)+\
                "\nOnlyK2: "+str(self.onlyk2)

def ParseResults(resultsFile):
    f = open(resultsFile, 'r') 
    lines = f.readlines()
    f.close()
    namePut = ""
    k = ""
    rounds = ""
    post = ""
    simplePost = ""
    newPut = True
    newCase = False
    checkResult = False
    getPost = True
    getRounds = True
    getSimplePost = True
    addCase = False
    addCaseForPUT = False
    put = None
    puts = []
    cases = []
    k1Disjunctive = False
    k2Disjunctive = False
    onlyK2Disjunctive = False
    forRealAddCase = False
    for i in range(0, len(lines)):
        line = lines[i]
        

        if 'PUT:' in line and newPut:
            
            newCase = True
            addCaseForPUT = True
            colonIdx = line.find(':')
            namePut = line[colonIdx+1 : -1]
            namePut = namePut.strip()
            #print("\n"+namePut)
            put = PUT(namePut)
            puts.append(put)
            #reset cases for new PUT
            cases = []
            k1Disjunctive = False
            k2Disjunctive = False
            onlyK2Disjunctive = False

        if 'Case: k ==' in line and newCase:
            newCase = False
            checkResult = True
            eqIdx = line.find('==')
            k = line[eqIdx+2:-1]
            k = k.strip()
            #print("case : " + k)
        
        if '===== Final Result' in line and checkResult:
            getPost = True
        
        if 'postcondition k ==' in line and getPost:
            getRounds = True
            post = lines[i+1].strip()
            post = post.strip()
            #print(post)
        
        if 'rounds:' in line and getRounds:
            getSimplePost = True
            getRounds = False
            colonIdx = line.find(':')
            rounds = line[colonIdx+1 : -1]
            rounds = rounds.strip()
            #print("rounds: " + rounds)

        if ('simplified post k ==' in line or 'simple' in line ) and getSimplePost:
            #reset the initial state at 'case k =='
            newCase = True
            addCase = True
            simplePost = lines[i+1]
            simplePost = simplePost.strip()
            #print(line)
            #print(simplePost)
            #case = Case(k,rounds,post,simplePost)
            #print(case)
            #print("\n")
        
        #consider refactoring so that the results of the implication are output at the end
        if 'Not(k0 -> k1)?' in line:
            questionIdx = line.find('?')
            res = line[questionIdx+1 : -1]
            res = res.strip()
            k1Disjunctive = (res == "sat")
            

        if 'Not(k0 -> k2)?' in line:
            forRealAddCase = True
            questionIdx = line.find('?')
            res = line[questionIdx+1 : -1]
            res = res.strip()
            onlyK2Disjunctive = (res == "sat")
            

        if 'Not(k1 -> k2)?' in line:
            questionIdx = line.find('?')
            res = line[questionIdx+1 : -1]
            res = res.strip()
            k2Disjunctive = (res == "sat")
            
        

        if addCase and forRealAddCase:
            # safe to assume implication results are ready to store
            addCase = False
            forRealAddCase = False
            case = Case(k,rounds,post,simplePost)
            cases.append(case)
            #update current PUT
            puts[len(puts)-1].addCases(cases)
            puts[len(puts)-1].k1 = k1Disjunctive
            puts[len(puts)-1].k2 = k2Disjunctive
            puts[len(puts)-1].onlyk2 = onlyK2Disjunctive 
    return puts

def printResults(puts: List[PUT] ):
    i = 0
    i = len(puts)-1
    for p in puts:
        if i < len(puts):
            print(p.putName)
        else:
            break
        i+=1
        j = 0
        j = len(p.getCases())-3
        for c in p.getCases():
            if j < len(p.getCases()):
                print(c)
                print("\n")
            else:
                break
            j += 1

    #with open(outputFile, "w") as f:
    #print("PUT: "+put.putName)
    #for c in put.getCases():
    #    print(c)
    #    print("")
def checkResults(regPuts: List[PUT], basePuts: List[PUT]):
    for rPut in regPuts:
        bPut = getPut(rPut.putName, basePuts)
        if not bPut is None:
            for rCase in rPut.getCases():
                bCase = getCase(rCase, bPut.getCases())
                if (not bCase is None) and not rCase == bCase:
                    print("Different cases for put: "+rPut.putName )
                    print("Base")
                    print(bCase)
                    print("")
                    print("Regression")
                    print(rCase)
                else:
                    print("matched case!")

        else:
            print("no PUT in base file")


def getCase(rCase: Type[Case], baseCases: List[Case]):
    ret = None
    for base in baseCases:
        if rCase.k == base.k:
            ret = base
    
    return ret


def getPut(name: str, basePut: List[PUT]):
    ret = None
    for base in basePut:
        if name == base.putName:
            ret =  base
    return ret



if __name__ == '__main__':
    resultFile = sys.argv[1]
    regressionResultFile = sys.argv[2]
    mode = sys.argv[3]

    if str(mode).upper() == "CHECK":
        puts = ParseResults(resultFile)
        regrePuts = ParseResults(regressionResultFile)
        checkResults(regrePuts, puts)
    
    if str(mode).upper() == "DISJUNC":
        puts = ParseResults(resultFile)
        for p in puts:
            print(p)
            print("")
    
    
    #printResults(puts)




