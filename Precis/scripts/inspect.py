#TODO: Ahmad change this so that you only read one "Problem" entry; of you see another Problem entry output a warning message but still create the inspection file 
# for the first problem
#Still need to label entries if alternate arguement is passed
SUBJECT = "SUBJECT"

class Contract:
    def __init__(self, name):
        self.name = name
        self.disjunctivity = ""
        self.cases = ""
        self.bestRefine = ""

    def __str__(self):
        return self.disjunctivity + self.cases

def getPath(file):
    import os
    return os.path.abspath(file)

def NewInspect(fileName, contracts, ovveride):
    import re
    path = getPath(fileName)
    initInspection = open(path, 'r')
    lines = initInspection.readlines()
    initInspection.close()
    header = lines[0]
    if not ovveride:
        spliceIndex = fileName.index("results")
        fileName = fileName[spliceIndex:]
        #newFileName = "CurrentInspections\inspected_" + fileName
        newFileName = "inspected_" + fileName
        readyInspection = open(newFileName, 'w')
        readyInspection.write(header)
    contracts[SUBJECT] = header
    predicate = "None"
    predicateRight = "None"
    predicateLeft = "None"
    currentContract = None
    resultSeen = False
    predicates = []
    rounds = ""
    sysnthesis_time = ""
    unique_features = ""
    synthesized_features = []
    total_rounds = 0
    total_pextime = 0
    total_learntime = 0
    for lineIndex in range(1, len(lines)):
        line = ""
        if "PUT: " in lines[lineIndex]:
            splitIndex = lines[lineIndex].index(":") + 1
            contract = lines[lineIndex][splitIndex:].lstrip().replace("\n", "")
            currentContract = Contract(contract)
            
            line = f"""
---------------------
{contract}
Disjunctive (PexChoose):
Disjunctive (Alternate Semantics):
Disjunctive (Truly):

smt check:

Truly Safe:

Analysis:
"""
            currentContract.disjunctivity = line
        if "Final Tree ====" in lines[lineIndex]:
            predicates = []
            while lineIndex < len(lines) and not "===== Final Result" in lines[lineIndex]:
                if "Predicate" in lines[lineIndex]:
                    predicates.append(lines[lineIndex])
                lineIndex += 1
        if "rounds" in lines[lineIndex] and not "max" in lines[lineIndex]:
                    #predicate = "None"
                    #predicateRight = "None"
                    #predicateLeft = "None"
                    splitIndex = lines[lineIndex].index(":") + 1
                    rounds = lines[lineIndex][splitIndex:].strip().replace("\n", "")
                    total_rounds += int(rounds)
        #currentContract.cases += line
        if "postcondition" in lines[lineIndex]:
            line = f"""
learned postcondition: {lines[lineIndex + 1]}"""
            currentContract.cases += line
        if "simplified post" in lines[lineIndex]:
            predicateStrings = "\n".join(predicates)
            line = f"""
simplified postcondition: {lines[lineIndex + 1]}
{predicateStrings}
rounds: {rounds}
"""     
            currentContract.cases += line
        if "pex time:" in lines[lineIndex]:
            splitIndex = lines[lineIndex].index(":") + 1
            pextime = lines[lineIndex][splitIndex:].strip().replace("\n", "")
            total_pextime += float(pextime)
            line = f"\n{lines[lineIndex]}"
            currentContract.cases += line
        if "learn time:" in lines[lineIndex]:
            splitIndex = lines[lineIndex].index(":") + 1
            learntime = lines[lineIndex][splitIndex:].strip().replace("\n", "")
            total_learntime += float(learntime)
            line = f"\n{lines[lineIndex]}"
            currentContract.cases += line
        if "Samples" in lines[lineIndex]:
            line = f"\n{lines[lineIndex]}"
            currentContract.cases += line
            contracts[currentContract.name] = currentContract
        if "synthesis time" in lines[lineIndex]:
            synthesis_time = f"{lines[lineIndex]}"
            currentContract.cases += synthesis_time
        if "unique features" in lines[lineIndex]:
            unique_features = f"{lines[lineIndex]}"
            currentContract.cases += unique_features
        if 'Synth Feature' in lines[lineIndex]:
            colon = lines[lineIndex].index(":")
            feature = lines[lineIndex][colon + 1:].strip()
            synthesized_features.append(feature)
        if "Problem" in lines[lineIndex]:
            print("WARNING:\n\tRegression contains more than one problem")
            break

        if not ovveride: readyInspection.write(line)
    line = f"""
======================
{synthesis_time}
{unique_features}
Synthesized Feautes:
    {synthesized_features}

Average Rounds: {total_rounds / (len(contracts) - 1)}

Average Pex Time: {total_pextime / (len(contracts) - 1)}

Average Learn Time: {total_learntime / (len(contracts) - 1)}
"""
    readyInspection.write(line)
    if not ovveride: readyInspection.close()

def OverrideInspections(fileName, oldSubject, newSubject):
    spliceIndex = fileName.index("results")
    fileName = fileName[spliceIndex:]
    newFileName = "CurrentInspections\inspected_" + fileName
    for contract in newSubject:
        if contract is SUBJECT:
            continue
        elif contract in oldSubject:
            oldSubject[contract] = newSubject[contract]
    readyInspection = open(newFileName, 'w')
    for contract in oldSubject:
        readyInspection.write(oldSubject[contract].__str__())    
    readyInspection.close()

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()                                               

    parser.add_argument("--mode", "-m", type=str, required=True)
    parser.add_argument("--regression-results", "-r", type=str, required=True)
    parser.add_argument("--old-regression-results", "-o", type=str, required=False)
    args = parser.parse_args()

    mode = args.mode
    regressionResults = args.regression_results
    oldRegressionResults = args.old_regression_results
    contracts = {}
    if mode == "New" or mode == "Override":
        NewInspect(regressionResults, contracts, False)
    if mode == "Override" and not oldRegressionResults is None:
        oldContracts = {}
        NewInspect(oldRegressionResults, oldContracts, True)
        OverrideInspections(oldRegressionResults, oldContracts, contracts)