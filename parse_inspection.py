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
                    json_result = {"smt": smt_result, tag+"_prefix_formula": prefix_formula, tag+"_formula": formula}
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
    

#Leaving all param as False because we currently only care about cases where precis is strictly better
def format_summary(result_json, all=False):
    res = ""
    for test, test_details in result_json.items():
        res += "Problem " + test + "\n\n"
        for file, file_details in test_details.items():
            if file_details['smt'] == "Precis" or (all and not file_details['smt']):
                res += "PUT_" + file + "\n"
                try:
                    res += "Precis post:" + file_details['precis_formula'] + "\n"
                except:
                    pass
                try: 
                    res += "Daikon post:" + file_details['daikon_formula'] + "\n"
                except:
                    pass
                res += "\n"
    return res
     

def get_file_names(dir):
    files  = (glob.glob(dir + '/inspected_results_*Test'))
    return set([os.path.basename(x) for x in files])
    # inspected_results_BinaryHeapTest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--precis", "-p", type=str, nargs=1, required=True)
    parser.add_argument("--daikon", "-d", type=str, nargs=1, required=True)
    parser.add_argument("--output", "-o", type=str, nargs=1, required=True)

    args = parser.parse_args()
    precis_dir = args.precis[0]
    daikon_dir = args.daikon[0]
    output_file = args.output[0]

    # precis_dir = "..\\ContractsSubjects\\Results\\Inspections\\CurrentInspections"
    # daikon_dir = "..\\ContractsSubjects\\Results\\Inspections\\DaikonInspections"
    # output_file = "result.txt"
    
    commonfiles = list((get_file_names(precis_dir)).intersection(get_file_names(daikon_dir)))
    precis_result = read_files(precis_dir, commonfiles, "precis")
    daikon_result = read_files(daikon_dir, commonfiles, "daikon")
    
    summary_result = merge(precis_result, daikon_result)
    result = format_summary(summary_result, all=True)
    
    with open(output_file, "w") as file:
        file.write(result)


# Sample run: python parse_inspection.py --precis  ..\\ContractsSubjects\\Results\\Inspections\\CurrentInspections --daikon ..\\ContractsSubjects\\Results\\Inspections\\DaikonInspections --output result.txt

main()