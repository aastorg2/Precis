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
import command_runner
from lxml import etree
from os.path import join
from z3 import *

from Data.problem import Problem
from Data.feature_vector import FeatureVector
from typing import List

class Pex:
    def __init__(self):
        self.binary = 'pex.exe'
        self.arguments = ['/nor']
        self.pexReportFormat = 'Xml'
        self.rn = "XmlReport"  
        self.ro = "root" 
        self.time = 0.0
        self.reportLocation = ""
        self.testsLocation = ""
    #def CreateTopLevelDirectories(problem, case)
    

    def RunTeacher(self, problem, PUTName, precisFeatureList) -> List[FeatureVector]:
        args = self.GetExecCommand(problem.testDll, PUTName, problem.testNamespace, problem.testClass)
        pexOutput = command_runner.runCommand(args)
        
        self.reportBaseLocation = problem.testDebugFolder
        self.reportLocation = os.path.join(self.reportBaseLocation, self.ro, self.rn, "report.per")
        self.testsLocation = os.path.join(self.reportBaseLocation, self.ro, self.rn, "tests")
        #print (self.time)

        return self.ParseReport(problem.testDebugFolder, precisFeatureList)

    def ParseReport(self, pexReportFolder, precisFeatureList):
        #This function should label the field testLabel for a feature vector object
        tree = etree.parse(self.reportLocation)
        dataPoints = list()
        featureValues = None
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
                    val = self.ReplaceIntMinAndMax(val)
                    val = self.ReplaceTrueAndFalse(val)
                    singlePoint = singlePoint + (val,)

            if test.get('status') == 'normaltermination':
                #singlePoint = singlePoint + ('True',)
                featureValues = FeatureVector(precisFeatureList, singlePoint, 'True')
            else:
                #Also for post condition learnig - consider checking that all the failures are of AssertionFailed type. 
                #singlePoint = singlePoint +('False',)
                # check for TermFailure exception
                if test.get('name').find("TermDestruction") != -1:
                    continue
                featureValues = FeatureVector(precisFeatureList, singlePoint, 'False')

            if len(singlePoint) < len(precisFeatureList):
                continue
            
            assert(featureValues != None)
            dataPoints.append(featureValues)
    
        return dataPoints

    def GetExecCommand(self, testDll, testMethod, testNamespace, testClass):
        cmd =[self.binary, testDll , '/membernamefilter:M:'+testMethod+'!', '/methodnamefilter:'+testMethod+'!', '/namespacefilter:'+testNamespace +'!', '/typefilter:'+testClass+'!']
        cmd.extend(['/ro:'+self.ro, '/rn:'+self.rn, '/rl:'+self.pexReportFormat])
        cmd.extend(self.arguments)
        
        return cmd
    
    def ReplaceIntMinAndMax(self, number):
        if number.find("int.MinValue") != -1:
            return "-2147483648"
        elif number.find("int.MaxValue") != -1:
            return "2147483647"
        return number
    
    def ReplaceTrueAndFalse(self, boolean):
        if boolean.upper() == 'TRUE':
            return 'True'
        elif boolean.upper() == 'FALSE':
            return 'False'
        else:
            return boolean


# if __name__ == '__main__':
#     # Better use absolute path here!!!
#     # Or VSCode might have some problem (the relative path depends on where you open the VSCode)
#     dll = '../ContractsSubjects/Stack/StackTest/bin/Debug/StackTest.dll'
#     testMethod = 'PUT_PushContract'
#     testNamespace = 'Stack.Test'
#     testType = 'StackContractTest'
#     pexReportFoler = '../ContractsSubjects/Stack/StackTest/bin/Debug/'

#     pex = Pex()
#     pex.RunTeacher(dll, testMethod, testNamespace, testType)
#     dataPoints = pex.ParseReportPost(pexReportFoler)
#     print(dataPoints)