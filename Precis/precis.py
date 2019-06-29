import os
from Data.problem import Problem



def learnPost():
    sln = os.path.abspath('../ContractsSubjects/Stack/Stack.sln')
    projectName =  'StackTest' 
    testFileName = 'StackContractTest.cs' 
    PUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']


    p = Problem(sln, projectName, testFileName, PUTs)
    print ("here")










if __name__ == '__main__':
    learnPost()