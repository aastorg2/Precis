import csv
import sys
from copy import *

def ParseContracts(resultsFile, outputFile):
    f = open(resultsFile, 'r') 
    lines = f.readlines()
    f.close()

    with open(outputFile, "w") as csvFile: 
        csvWriter = csv.writer(csvFile)
        
        idx = 0
        while idx < len(lines):
            line = lines[idx]
            if 'PUT_' in line:
                PUTName = line[5:-1]
                csvWriter.writerow([PUTName, "Postcondition","Rounds", "Not(k0->k1)", "Not(k1->k2)","Not(k0->k2)" ])
            
            elif 'postcondition k == ' in line :
                strIdx = line.find('k ==')
                str1 = line[strIdx : -1]
                str2 = lines[idx + 1]
                str3 = lines[idx + 2]
                #csvWriter.writerow([str1, str2.strip(), str3[str3.find(':')+1: ].strip()])
                
                #idx += 1
            
            elif 'simple   post k ==' in line: 
                strIdx = line.find('simple')
                str1 = line[strIdx :strIdx+ 6]
                str2 = lines[idx + 1]
                str3 = lines[idx + 2]
                csvWriter.writerow([str1,str2.strip(), str3[str3.find(':')+1: ].strip()])
                #idx += 1
            idx += 1

if __name__ == '__main__':
    resultFile = sys.argv[1]
    outputFile = sys.argv[2]
    ParseContracts(resultFile, outputFile)
