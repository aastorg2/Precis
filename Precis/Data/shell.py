import os
from os import sys, path
import io
import subprocess
import re
import platform
import Teachers.command_runner

class Shell:

    isWindows = True


    def __init__(self, windows):
        self.isWindows = windows

    
    def removeSygusFile(self, location, fileEndingPattern):
        
        if self.isWindows:
            absolutePath = path.abspath(location)
            try:
                if path.exists(absolutePath):
                    for f in os.listdir(absolutePath):
                        if re.search(fileEndingPattern, f):
                            os.remove(os.path.join(location, f))
            except:
                assert(False), "something went wrong in deleting sygus file"

    def writeToFile(self, location, fileName, fileContents):
        if self.isWindows:
            absPath = os.path.abspath(location + '/' + fileName).strip()
            # print absPath
            #wb to output LF, w outputs CRLF
            with open(absPath, 'w',newline='\n',) as outfile:
                outfile.write(fileContents.replace('\r\n',r'\n'))
            
            #unixPath = self.runCommand( Shell.wslBin() + ' wslpath -a \'' + absPath + '\'')
            #print(str(unixPath, 'utf-8'))

            #sys.exit(0)
        else:
            assert(False), "This method is meant to write to file in windows shell"
    
    

    def getAbsolutePathByOs(self, path, osType):
        try:
            absPath = os.path.abspath(path).strip()

            if osType == "windows" or osType == "win":
                return absPath
            elif osType == "linux" or osType == "wsl":
                # git linux path by calling wsl -a
                print(Shell.wslBin() + ' wslpath -a \'' + absPath + '\'')
                
                return self.runCommand( Shell.wslBin() + ' wslpath -a \'' + absPath + '\'')
        except Exception as ex:
            Shell.printExceptionAndExit(ex, "Error Converting Path")

    @staticmethod
    def wslBin():
        is32bit = (platform.architecture()[0] == '32bit')
        system32 = os.path.join(os.environ['SystemRoot'], 
                            'SysNative' if is32bit else 'System32')
        wsl = os.path.join(system32, 'wsl.exe')
        return wsl

    @staticmethod
    def printExceptionAndExit(e, msg):
        raise Exception(str(e) + ": " + msg)

    def runCommand(self,args, directory = '.'):
        try:
            # #remove any starting with wsl
            # if self.osType == "windows":
            #     args = re.sub('\s*(wsl\s+)*(.*)', '\g<2>', args)
            # # add wsl if needed
            # elif self.osType == "linux":
            #     args = re.sub('\s*(wsl\s+)*(.*)', 'wsl \g<2>', args)

            # print("Executing:", args)
            executionOutput = ""
            #print("command: ", args)
            executionRun = subprocess.Popen(args, cwd = directory, stdout = subprocess.PIPE, stderr = subprocess.PIPE)
            # TODO: concatenating executionRun.stdout is bytes and the for loop iterates over a byte string
            for line in executionRun.stdout:
                line = line.decode('utf-8')
                executionOutput = executionOutput + os.linesep + str(line.rstrip())
            
            executionOutput = executionOutput.strip()
            executionRun.stdout.close()
            # print("Output:", executionOutput)
            return executionOutput

        except Exception as e:
            print(executionOutput)
            Shell.printExceptionAndExit(e, "Execution Error")