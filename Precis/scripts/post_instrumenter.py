import argparse
from instrumenter import Instrumenter
import os
from problem import Problem

def get_problem(tool, problem_name):
    tool = "Daikon" if tool == "Daikon" else ""
    sln = os.path.abspath(f'../{tool}ContractsSubjects/{problem_name}/{problem_name}.sln')
    projectName = f'{problem_name}Test'
    testDebugFolder = f'../{tool}ContractsSubjects/{problem_name}/{problem_name}Test/bin/Debug/'
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
    

    return p


def get_name(line):
    #Problem: ArrayListTest
    colon = line.index(":") + 1
    test = line.index("Test")
    return line[colon:test].strip()


def instrument_posts(tool, inspection):
    instrumenter = Instrumenter("C:\Windows\Microsoft.NET\Framework\\v4.0.30319\MSBuild.exe", "../Precis/Instrumenter/Instrumenter/bin/Debug/Instrumenter.exe")

    i_file = open(inspection, 'r')
    lines = i_file.readlines()
    i_file.close()

    put_posts = extract_posts(lines)
    problem = get_problem(tool, get_name(lines[0]))

    for put_name in put_posts:
        instrumenter.instrumentPostString(problem, put_posts[put_name], put_name)


def extract_posts(lines):
    idx = 0
    posts = {}
    current_contract = ""
    while idx < len(lines):
        if "PUT_" in lines[idx]:
            current_contract = lines[idx].strip()
        if "simplified:" in lines[idx]:
            colon = lines[idx].index(':') + 1
            post = lines[idx][colon:].strip()
            posts[current_contract] = post
        idx += 1
    return posts


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("--precis", "-p", type=str, required=False)
    parser.add_argument("--daikon", "-d", type=str, required=False)

    args = parser.parse_args()

    precis_inspections = args.precis
    daikon_inspections = args.daikon

    if precis_inspections == None and daikon_inspections == None:
        print("NOTHING TO INSTRUMENT...")

    if not precis_inspections == None:
        instrument_posts("Precis", os.path.abspath(precis_inspections))

    if not daikon_inspections == None:
        instrument_posts("Daikon", os.path.abspath(daikon_inspections))