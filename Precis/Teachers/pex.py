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

class Pex:
    def __init__(self):
        self.binary = 'pex.exe'
        self.arguments = ['/nor']
        self.pexReportFormat = 'Xml'
        self.rn = "XmlReport"  
        self.ro = "r1" 
        self.time = 0.0

    def RunTeacher(self, problem, PUTName, pvarList):
        self.time = 0.0
        startTime = time.time()
        args = self.GetExecCommand(problem.testDll, PUTName, problem.testNamespace, problem.testClass)
        pexOutput = command_runner.runCommand(args)
        self.time = time.time() - startTime
        print (self.time)

        return self.ParseReport(problem.testDebugFolder, pvarList)

    def ParseReport(self, pexReportFolder, pvarList):
        pexReportFile = os.path.join(pexReportFolder, self.ro, self.rn, "report.per")
        tree = etree.parse(pexReportFile)
        dataPoints = set()
        for test in tree.xpath('//generatedTest'):
            # REMIENDER: will need to add more cases for pex internal failures such as the above. We do not want to create feature from these values
            if test.get('status') == 'assumptionviolation' or test.get('status') == 'minimizationrequest':
                continue
            
            singlePoint = ()
            for value in test.xpath('./value'):
                if re.match("^\$.*", value.xpath('./@name')[0]):
                    val = str(value.xpath('string()'))
                    val = self.ReplaceIntMinAndMax(val)
                    val = self.ReplaceTrueAndFalse(val)
                    singlePoint = singlePoint + (val,)

            if test.get('status') == 'normaltermination':
                singlePoint = singlePoint + ('True',)

            else:
                singlePoint = singlePoint +('True',)
                
            if len(singlePoint) < len(pvarList):
                continue
            dataPoints.add(FeatureVector(pvarList, singlePoint))
    
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