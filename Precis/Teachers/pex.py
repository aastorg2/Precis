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
import executecommand
from lxml import etree
from os.path import join
from z3 import *

class Pex:
    def __init__(self, binary, numVariables, arguments):
        self.binary = binary
        self.arguments = arguments
        self.numVariables = numVariables
        self.pexReportFormat = 'Xml'
        self.rn = "XmlReport"  
        self.ro = "r1" 
        self.time = 0.0

    def RunTeacher(self, dll, testMethod, testNamespace, testType):
        self.time = 0.0
        startTime = time.time()
        args = self.GetExecCommand(dll, testMethod, testNamespace, testType)
        pexOutput = executecommand.runCommand(args)
        self.time = time.time() - startTime
        
    def ParseReportPre(self, pexReportFolder):
        pexReportFile = os.path.join(pexReportFolder, self.ro, self.rn, "report.per")
        tree = etree.parse(pexReportFile)
        dataPoints = []
        for test in tree.xpath('//generatedTest'):
            singlePoint = []
            for value in test.xpath('./value'):
                if re.match("^\$.*", value.xpath('./@name')[0]):
                    singlePoint.append(str(value.xpath('string()')))

            if test.get('status') == 'normaltermination':
                singlePoint.append('true')
            elif test.get('status') == 'assumptionviolation':
                continue
            elif test.get('status') == 'minimizationrequest':
                continue
            # REMIENDER: will need to add more cases for pex internal failures such as the above. We do not want to create feature from these values
            else:
                singlePoint.append('false')
            # alternatives: test.get('failed') => true / None
            # exceptionState
            # failureText
            dataPoints.append(singlePoint)
            
        return dataPoints

    # refactor this later
    def ParseReportPost(self, pexReportFolder):
        if True:  #learner.name == "HoudiniExtended":
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
                        singlePoint = singlePoint + (val,)

                if test.get('status') == 'normaltermination':
                    singlePoint = singlePoint + ('true',)

                else:
                    # Houdini - Only positive points
                    singlePoint = singlePoint +('true',)
                    
                if len(singlePoint) < self.numVariables:
                    continue
                dataPoints.add(singlePoint)
            
            return dataPoints

    def GetExecCommand(self,testDll, testMethod, testNamespace, testType):
        cmd_exec =[self.binary, testDll , '/membernamefilter:M:'+testMethod+'!', '/methodnamefilter:'+testMethod+'!', '/namespacefilter:'+testNamespace +'!', '/typefilter:'+testType+'!']
        cmd_exec.extend(['/ro:'+self.ro, '/rn:'+self.rn, '/rl:'+self.pexReportFormat])
        cmd_exec.extend(self.arguments)
        
        return cmd_exec
    
    def ReplaceIntMinAndMax(self, number):
        if number.find("int.MinValue") != -1:
            return "-2147483648"
        elif number.find("int.MaxValue") != -1:
            return "2147483647"
        return number

if __name__ == '__main__':
    # Better use absolute path here!!!
    # Or VSCode might have some problem (the relative path depends on where you open the VSCode)
    dll = '../ContractsSubjects/Stack/StackTest/bin/Debug/StackTest.dll'
    testMethod = 'PUT_PushContract'
    testNamespace = 'Stack.Test'
    testType = 'StackContractTest'
    pexReportFoler = '../ContractsSubjects/Stack/StackTest/bin/Debug/'

    pex = Pex('pex.exe', 8, ['/nor'])
    pex.RunTeacher(dll, testMethod, testNamespace, testType)
    dataPoints = pex.ParseReportPost(pexReportFoler)
    print(dataPoints)