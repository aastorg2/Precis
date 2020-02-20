import os
from os import sys, path
import shutil
import logging

logger = logging.getLogger("Results.evaluation")

#refactor so that there is only one createDirectory function

def createDirectoryForTests(mainDir, projectName, putName, case):
    rootDirForTests = os.path.abspath(mainDir)
    locationOfTests = os.path.join(rootDirForTests, projectName,putName,case)
    if path.exists(locationOfTests):
        shutil.rmtree(locationOfTests)
    os.makedirs(locationOfTests)
    return locationOfTests

def createDirectoryForTestsWithoutCase(mainDir, projectName, putName):
    rootDirForTests = os.path.abspath(mainDir)
    locationOfTests = os.path.join(rootDirForTests, projectName,putName)
    if path.exists(locationOfTests):
        shutil.rmtree(locationOfTests)
    os.makedirs(locationOfTests)
    return locationOfTests

def copyTestFilesToEvaluationDir(source, dest, round):
    
    targetDirName = os.path.basename(os.path.normpath(source))
    dest = os.path.join(dest, targetDirName+str(round))
    try:
        shutil.copytree(source, dest)
    # Directories are the same
    except shutil.Error as e:
        logger.info('Directory not copied. Error: '+ str(e))
        print('Directory not copied. Error: %s' % e)
    # Any error saying that the directory doesn't exist
    except OSError as e:
        logger.info('Directory not copied. Error: '+ str(e))
        print('Directory not copied. Error: %s' % e)

#def createDirectory()


