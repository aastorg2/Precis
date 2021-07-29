import subprocess
import sys
import re
import os
import time
import argparse
import collections
import pprint
import csv
import json
import time
import shutil
import io
import platform
from test import Test
from xml.etree import ElementTree as ET
from precis_feature import PrecisFeature
from problem import Problem
from typing import List, Tuple, Type
from lxml import etree

# CONSTANTS #
WINDOWS = "Windows"

# Returns the absolute path to a file or directory
def get_abs_path(path: "str"):
    return os.path.abspath(path)

# rename contract_test to test_file
# NOTE consider if we parse PUT names then for safety check, the xml parsing will have to consider that pex will output
# of each test in seperate .cs files
# Method that handles setting up pex, rebuilding the solution and running pex
def run(tool, subject, inspection, include, restore):
    problem, subjectRootDir = get_problem(tool, subject)
    # Replace all [PexMethod]
    test_file = f"C:/Users/12247/Research/{subjectRootDir}/{subject}/{subject}Test/{subject}ContractTest.cs"
    pex_replacement(test_file, restore)
    # Build solution
    build(problem.sln)
    # Run pex per put
    contracts = dict()
    if not include:
        include = problem.puts
    for putName in include:
        putBaseFeat = getBaseFeatures(tool, problem, putName)
        tests, total, passing, failing = run_pex(problem.sln, problem.testDll, putName, subjectRootDir, putBaseFeat, inspection) # puts as contracts
        contracts[putName] = (tests, total, passing, failing)
    return contracts

# Method to set up pex config
def pex_replacement(test_file: "str", restore: "bool"):
    abs_path_to_test_file = get_abs_path(test_file)
    # What you wish to replace
    reg = "\s*(\[PexMethod.*\])"
    # What you wish to replace with
    # %Timeout = 500 sec. (default:120)
    # %MaxConstraintSolverTime = 10 sec. (default:2)
    # %MaxRunsWithoutNewTests = 2147483647 (default:100)
    # %MaxRuns = 2147483647 (default:100)
    # [PexMethod(Timeout = 500, ...,... ) ]
    replacement = "[PexMethod(Timeout = 500, MaxConstraintSolverTime = 10, MaxRunsWithoutNewTests = 2147483647, MaxRuns = 2147483647)]"
    if restore:
        temp = reg
        reg = replacement
        replacement = temp
    # Reads the file
    file = open(abs_path_to_test_file, 'r')
    lines = file.readlines()
    file.close()
    # Performs replacement
    # Writes chaages to the contract test
    file = open(abs_path_to_test_file, 'w')
    for idx in range(0, len(lines)):
        match = re.findall(reg, lines[idx])
        if len(match) > 0:
            lines[idx] = lines[idx].replace(match[0], replacement)
        file.write(lines[idx])
    file.close()


# Builds the solution
def build(solution: "str"):
    build_command = get_msbuild_command(solution)
    build_output = run_command(build_command)


# Gets the build command to run
def get_msbuild_command(solution: "str"):
    abs_path_to_solution = get_abs_path(solution)
    abs_path_to_msbuild = get_abs_path("c:\WINDOWS\Microsoft.NET\Framework\\v4.0.30319\MSBuild.exe")
    return f"{abs_path_to_msbuild} {abs_path_to_solution} /t:rebuild"


def getBaseFeatures(tool, problem, PUTName):
    AllOberverTypes = os.getcwd()
    AllOberverTypes = AllOberverTypes+"\\typesOM_Class.txt"
    putObeserverTypes = os.getcwd()
    putObeserverTypes = putObeserverTypes +"\\typesOM_PUT.txt"
    precisObserverTypes = os.getcwd()
    precisObserverTypes = precisObserverTypes + "\\typesOM.txt"

    if tool == "Daikon":
        problem.ExtractObserversInClass(AllOberverTypes, "daikonClass")
        problem.ExtractObserversInPUT(PUTName, putObeserverTypes,"daikonMethod")
        # allFeatures: Tuple[PrecisFeature] = problem.ReadObserversFromFile(AllOberverTypes)
        putBaseFeatures: Tuple[PrecisFeature] = problem.ReadObserversFromFile(putObeserverTypes)
    else:
        problem.ExtractObservers(PUTName, precisObserverTypes, "precis")
        putBaseFeatures: Tuple[PrecisFeature] = problem.ReadObserversFromFile(precisObserverTypes)

    # print(allFeatures)
    # print(putBaseFeatures)

    return putBaseFeatures


def get_problem(tool, problem_name):
    tool = "Daikon" if tool == "Daikon" else ""
    subjectRootDir = f"{tool}ContractsSubjects"
    sln = os.path.abspath(f'../{subjectRootDir}/{problem_name}/{problem_name}.sln')
    projectName = f'{problem_name}Test'
    testDebugFolder = f'../{subjectRootDir}/{problem_name}/{problem_name}Test/bin/Debug/'
    testDll = testDebugFolder + f'{problem_name}Test.dll'
    testFileName = f'{problem_name}ContractTest.cs'
    testNamepace = f'{problem_name}.Test'
    testClass = f'{problem_name}ContractTest'
    daikonTestFilePath = f"../DaikonContractsSubjects/{problem_name}/{problem_name}Test/{problem_name}DaikonContract.cs" if tool == "Daikon" else ""

    arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract',
                     'PUT_GetContract', 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']

    binaryHeapPUTs = ['PUT_AddContract', 'PUT_MinimumContract', 'PUT_RemoveMinimumContract', 'PUT_RemoveAtContract',
                     'PUT_IndexOfContract', 'PUT_UpdateContract', 'PUT_MinimumUpdateContract']
    
    dictionaryPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_GetContract', 'PUT_SetContract', 'PUT_ContainsKeyContract', 'PUT_ContainsValueContract', 'PUT_CountContract']
    
    hashSetPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_CountContract', 'PUT_ContainsContract']

    queuePUTs = ['PUT_EnqueueContract', 'PUT_DequeueContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']

    stackPUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_ContainsContract', 'PUT_CountContract']

    uGraphPUTS = ['PUT_AddVertexContract', 'PUT_RemoveVertexContract', 'PUT_ClearAdjacentEdgesContract','PUT_ContainsEdgeContract',
                    'PUT_ContainsEdgeIntContract', 'PUT_AdjacentEdgeContract', 'PUT_IsVerticesEmptyContract', 'PUT_VertexCountContract', 'PUT_ContainsVertexContract',
                    'PUT_AddEdgeContract', 'PUT_RemoveEdgeContract', 'PUT_IsEdgesEmptyContract', 'PUT_EdgeCountContract', 'PUT_AdjacentDegreeContract',
                    'PUT_IsAdjacentEdgesEmptyContract']

    puts_map = {"ArrayList": arrayListPUTs, "BinaryHeap": binaryHeapPUTs, "Dictionary": dictionaryPUTs, "HashSet": hashSetPUTs, "Queue": queuePUTs,
                "Stack": stackPUTs, "UndirectedGraph": uGraphPUTS}

    PUTs = puts_map[problem_name]

    p = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass, daikonTestFilePath, PUTs)
    

    return p, subjectRootDir


# Runs pex on each contract and returns a list of generated tests
def run_pex(solution:"str", assembly: "str", contract: "str", subjectRootDir: "str", feat_list: "list", inspection): # puts as parameter
    # The absolute path to the dll
    abs_path_to_assembly = get_abs_path(assembly)
    # Get the problem information for pex
    (problem_name, test_namespace, test_class) = get_problem_information(solution,subjectRootDir)
    # For each contract, run pex
    pex_command = get_pex_command(abs_path_to_assembly, contract, test_namespace, test_class)
    # Store the pex output for that contract
    pex_output = run_command(pex_command)
    # Parse and store each generated test in a list
    # Assumes root directory is named root
    (path_to_tests, path_to_report) = get_path_to_xml_report(abs_path_to_assembly, problem_name)
    (total, passing, failing) = parse_report(contract, path_to_report, feat_list, inspection)
    tests = collect_tests(contract, path_to_tests)
    return (tests, total, passing, failing)


# Returns the path to the directory that contains the XmlReport pex generated
def get_path_to_xml_report(path_to_assembly: "str", problem_name: "str"):
    delimiter = "\\" if platform.system() is WINDOWS else '/'
    root_dir = delimiter + "root"
    slice_index = path_to_assembly.rindex(delimiter)
    path_to_root_dir = path_to_assembly[:slice_index] + root_dir
    dirs = os.listdir(path_to_root_dir)
    # Makes sure pex geneerated an xml report
    assert("XmlReport" in " ".join(dirs))
    path_to_tests = f"{path_to_root_dir + delimiter}XmlReport{delimiter}tests{delimiter + problem_name + delimiter}Test{delimiter}"
    path_to_report = f"{path_to_root_dir + delimiter}XmlReport{delimiter}report.per"
    return (path_to_tests, path_to_report)


# Parses the xml report file generated by pex and prints the results to stdout
def parse_report(contract: "str", report: "str", feat_list: "list", inspection):
    with open(inspection) as f:
        i_lines = f.readlines()
    
    # Information to print to stdout
    number_of_tests_generated = int()
    number_of_passing_tests = int()
    number_of_failing_tests = int()

    tree = etree.parse(report)
    featureValues = None
    alreadyMarkedFalse = False
    for test in tree.xpath('//generatedTest'):
        # REMIENDER: will need to add more cases for pex internal failures such as the above. We do not want to create feature from these values
        if test.get('status') == 'assumptionviolation' or test.get('status') == 'minimizationrequest':
            continue
        if test.get('status') == 'pathboundsexceeded':
            print("ideally, this test should be re-ran since path bounds exceeded")
            continue
        singlePoint = ()
        for value in test.xpath('./value'):
            if re.match("^\$.*", value.xpath('./@name')[0]):
                val = str(value.xpath('string()'))
                val = ReplaceIntMinAndMax(val)
                val = ReplaceTrueAndFalse(val)
                singlePoint = singlePoint + (val,)
        
        if len(singlePoint) < len(feat_list):
            continue
        
        name = test.get('name')
        
        if test.get('status') == 'normaltermination':
            number_of_tests_generated += 1
            number_of_passing_tests += 1
            #singlePoint = singlePoint + ('True',)
        elif "TermDestruction" in name:
            #Also for post condition learnig - consider checking that all the failures are of AssertionFailed type. 
            #singlePoint = singlePoint +('False',)
            # check for TermFailure exception
            continue
        elif "PexAssertFailed" in name:
            if not alreadyMarkedFalse:
                contract_pos_in_name = name.index("Contract") 
                
                put = name[:contract_pos_in_name]
                
                put_found = False
                
                for line_idx in range(len(i_lines)):
                    put_found = put in i_lines[line_idx] or put_found
                    
                    if put_found and "Truly Safe" in i_lines[line_idx]:
                        colon = i_lines[line_idx].index(":")
                        i_lines[line_idx] = i_lines[line_idx][:colon + 1] + " False\n"
                        break
                
                alreadyMarkedFalse = True
            
            number_of_tests_generated += 1
            number_of_failing_tests += 1
    
    with open(inspection, 'w') as f:
        f.write("".join(i_lines))
        

    print(f"{contract}:")
    print(f"\tNumber of tests generated: {number_of_tests_generated}")
    print(f"\tNumber of passing tests: {number_of_passing_tests}")
    #number_of_failing_tests = number_of_tests_generated - number_of_passing_tests
    print(f"\tNumber of failing tests: {number_of_failing_tests}\n")

    return (number_of_tests_generated, number_of_passing_tests, number_of_failing_tests)


def ReplaceIntMinAndMax(number):
        if number.find("int.MinValue") != -1:
            return "-2147483648"
        elif number.find("int.MaxValue") != -1:
            return "2147483647"
        return number
    

def ReplaceTrueAndFalse(boolean):
    if boolean.upper() == 'TRUE':
        return 'True'
    elif boolean.upper() == 'FALSE':
        return 'False'
    else:
        return boolean


# Parses the tests files and stores them in a list
def collect_tests(contract: "str", path_to_tests: "str"):
    tests = list()
    slice_index = contract.index("Contract")
    name_of_PUT = contract[:slice_index]
    
    for test in os.listdir(path_to_tests):
        file_ending = test.index(".g.cs")
        put_index = test.index("PUT")
        test_name = test[put_index:file_ending]
        if not test_name in name_of_PUT and name_of_PUT not in test_name:
            continue
        # Get the absolute path to the test
        path_to_current_test = path_to_tests + test
        # Read the test
        file = io.open(path_to_current_test, encoding="utf-16")
        lines = "".join(file.readlines())
        file.close()
        # Parse test
        test_attribute = "[TestMethod]" if len(lines.split("[Test]")[1:]) == 0 else "[Test]"
        new_tests = lines.split(test_attribute)[1:]
        for idx in range(0, len(new_tests) - 1):
            new_tests[idx] = new_tests[idx].replace("\n\n        ", "")
        new_tests[len(new_tests) - 1] = new_tests[len(new_tests) - 1].replace("\n    }\n}\n", "")
        for idx in range(0, len(new_tests)):
            new_tests[idx] = Test(test_attribute, new_tests[idx])
        tests.extend(new_tests)
    return tests



# Gets the information that pex needs to run
def get_problem_information(solution: "str", rootSubjectDir: "str"):
    abs_path_to_solution = get_abs_path(solution)
    delimiter = "\\" if platform.system() is WINDOWS else '/'
    contracts_subjects = f"{delimiter}{rootSubjectDir}{delimiter}"
    slice_index = abs_path_to_solution.index(contracts_subjects)
    problem_name = abs_path_to_solution[slice_index+len(contracts_subjects):]
    slice_index = problem_name.index(delimiter)
    problem_name = problem_name[:slice_index]
    return (problem_name, f"{problem_name}.Test", f"{problem_name}ContractTest")


# Returns the command to run pex with
def get_pex_command(testDll: "str", testMethod: "str", testNamespace: "str", testClass: "str"):
        arguments = ['/nor']
        abs_path_to_pex = get_abs_path("c:\Program Files\Microsoft Pex\\bin\pex.exe") # Might not work on systems other than windows...
        cmd = [abs_path_to_pex, testDll , f"/membernamefilter:M:{testMethod}!", f"/methodnamefilter:{testMethod}!", f"/namespacefilter:{testNamespace}!", f"/typefilter:{testClass}!"]
        cmd.extend(["/ro:root", "/rn:XmlReport", "/rl:Xml"])
        cmd.extend(arguments)
        
        return cmd


# Runs the passed in command
def run_command(args):
    try:
        executionOutput = ""
        executionRun = subprocess.Popen(args, stdout = subprocess.PIPE, stderr = subprocess.PIPE)
        for line in executionRun.stdout:
            executionOutput += os.linesep + str(line.rstrip())
        executionRun.stdout.close()
        return executionOutput
    except OSError as e:
        print('OSError > ', e.errno)
        print('OSError > ', e.strerror)
        print('OSError > ', e.filename)       
        raise OSError
    except:
        print('Error > ', sys.exc_info()[0])
        raise OSError


# Main Method
if __name__ == "__main__":
    # Create the argument parser
    parser = argparse.ArgumentParser()
    # Argument that collects the contract test, the solution, and the test dll
    parser.add_argument("--tool", '-t', type=str, required=True)
    parser.add_argument("--subject", '-s', type=str, required=True)
    parser.add_argument("--inspection", type=str)
    parser.add_argument("--include", '-i', default=False, action='store_true')
    parser.add_argument("--restore", "-r", type=str, nargs=argparse.ONE_OR_MORE, required=False)
    # Produces a namespace that maps 'run' to a list filled with the arguments
    args = parser.parse_args()
    # Get the tool used (Precis or Daikon)
    tool = args.tool
    # Get the subject
    subject = args.subject
    # get the contracts user wants to run specifically
    include = args.include
    # if true => restores the pex attributes to original values
    restore = args.restore
    inspection = args.inspection
    run(tool, subject, inspection, include, restore)

    # for test in tests:
    #     print(test)




    