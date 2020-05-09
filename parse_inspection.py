import re
import argparse
import os
import glob


def extract(regex, text):
    found = ""
    try:    
        m = re.search(regex, text)
        if m:
            found = m.group(1)
    except: 
        found = "" 
        
    return found


def read_files(dir, files, tag):
    result = {} 
    for file in files: 
        path = os.path.join(dir, file)
        with open(path, 'r') as file:
            content = file.read()
            problem = extract("Problem: (.*)\s", content)
            result[problem] = {}
            split_benchmarks = content.split("---------------------")
            for benchmark in split_benchmarks:
                try:
                    name = extract("PUT_(.*)\s", benchmark)
                    if not name:
                        continue
                    smt_result = extract("smt check:\s?(.*)\s", benchmark)
                    formula = extract("CNF simplified:(.*)\s", benchmark)
                    prefix_formula = extract("CNF simplified \(smt\):(.*)\s", benchmark)
                    json_result = {"smt": smt_result, tag+"_prefix_formula": prefix_formula, tag+"_formula": formula, "name": name}
                    result[problem][name] = json_result
                except:
                    pass
                
    return result
    

def merge(a, b):
    "merges b into a"
    for key in b:
        if key in a:
            if isinstance(a[key], dict) and isinstance(b[key], dict):
                merge(a[key], b[key])
            elif a[key] == b[key]:
                pass # same leaf value
            else:
                a[key] = "Conflict:" + str(a[key]) + " and " + str(b[key])
        else:
            a[key] = b[key]
    return a
    

def format_summary(result_json, rules):
    result = [""]*len(rules)
    for test, test_details in result_json.items():
        result[:] = [ res + "Problem " + test + "\n\n" for res in result]
        for file, file_details in test_details.items():
            for index, fn in enumerate(rules):
                try:
                    result[index] += fn(file_details)
                except: 
                    pass
    
    for index, fn in enumerate(rules):
        with open("summary_" + fn.__name__ +".txt", "w") as file:
            file.write(result[index])
    

def get_file_names(dir):
    files  = (glob.glob(dir + '/inspected_results_*Test'))
    return set([os.path.basename(x) for x in files])
    # inspected_results_BinaryHeapTest





# ====================Rules==================== #

def print_file_details(file_details):
    res = "PUT_" + file_details["name"] + "\n"
    res += "Precis post:" + file_details['precis_formula'] + "\n"
    res += "Daikon post:" + file_details['daikon_formula'] + "\n"
    res += "\n"
    return res


def all_benchmarks(file_details):
    return print_file_details(file_details)


def precis_stronger(file_details):
    res = ""
    if file_details['smt'] == "Precis":
        res = print_file_details(file_details)
    return res
    

def daikon_true(file_details):
    res = ""
    if "true" in file_details['daikon_formula']:
        res = print_file_details(file_details)
    return res


def precis_disjunct(file_details):
    res = ""
    if "||" in file_details['precis_formula'] and "||" not in file_details['daikon_formula']:
        res = print_file_details(file_details)
    return res


def common_predicates(file_details):
    def tokenize(formula):
        return set([ x.strip() for x in formula.replace("(", "").replace(")", "").split("&&")]) 
   
    def tokens_to_string(tokens):
        return " && ".join(list(tokens))
    
    res = ""
    if "||" not in file_details['precis_formula'] and "||" not in file_details['daikon_formula'] and "true" not in file_details['daikon_formula']:
        res += "PUT_" +  file_details["name"] + "\n"
        precis_set = tokenize(file_details['precis_formula'])
        daikon_set = tokenize(file_details['daikon_formula'])
        intersect = precis_set.intersection(daikon_set)
        
        res += "Precis post: " + tokens_to_string(intersect) + " && **" +  tokens_to_string(precis_set.difference(intersect)) + "**\n"
        res += "Daikon post: " + tokens_to_string(intersect) + " && **" +  tokens_to_string(daikon_set.difference(intersect)) + "**\n"
        res += "\n"
    return res
    


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--precis", "-p", type=str, nargs=1, required=True)
    parser.add_argument("--daikon", "-d", type=str, nargs=1, required=True)

    args = parser.parse_args()
    precis_dir = args.precis[0]
    daikon_dir = args.daikon[0]

    # precis_dir = "..\\ContractsSubjects\\Results\\Inspections\\CurrentInspections"
    # daikon_dir = "..\\ContractsSubjects\\Results\\Inspections\\DaikonInspections"
    
    commonfiles = list((get_file_names(precis_dir)).intersection(get_file_names(daikon_dir)))
    precis_result = read_files(precis_dir, commonfiles, "precis")
    daikon_result = read_files(daikon_dir, commonfiles, "daikon")
    
    summary_result = merge(precis_result, daikon_result)
    
    rules = [all_benchmarks, precis_stronger, daikon_true, precis_disjunct, common_predicates]
    format_summary(summary_result, rules)


# Sample run: python parse_inspection.py --precis  ..\\ContractsSubjects\\Results\\Inspections\\CurrentInspections --daikon ..\\ContractsSubjects\\Results\\Inspections\\DaikonInspections 

main()
