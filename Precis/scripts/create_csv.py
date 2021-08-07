import argparse
import csv
import os

def main(inspections):
  
  fieldnames = ['Contracts', 'Safe_MAN', 'Strength_vs_daikon','Strength_vs_predicate_synthesis', 'Strength_vs_conjunc'] #TODO add SAFE_TG
  
  with open('results.csv', 'w') as csv_file:
    writer = csv.DictWriter(csv_file, fieldnames)
    writer.writeheader()
  
    for inspection in inspections:
    
      path = os.path.abspath(inspection)
      
      with open(path) as f:
        lines = f.readlines()
        
      rows = get_row(lines)
      writer.writerows(rows)
      

def get_row(lines):
  rows = []
  row = {}
  for line in lines:
    if "Problem" in line:
      info = get_info_from_line(line)
      info = info.replace("Test", "") # Just want the name of the subject
      rows.append({'Contracts': info, 'Safe_MAN': '', 'Strength_vs_daikon': '','Strength_vs_predicate_synthesis': '', 'Strength_vs_conjunc': ''})
      continue
    if '----' in line and row:
      rows.append(row)
      row = {}
    elif "Truly Safe" in line:
      info = get_info_from_line(line)
      if info != '':
        info = 'yes' if eval(info) else 'no'
      row['Safe_MAN'] = info
    elif "smt check" in line:
      info = get_info_from_line(line)
      info = info if not info == "Daikon" else "Other"
      # row['Strength'] = info
    elif "PUT" in line:
      info = line.strip()
      row['Contracts'] = info
  return rows


def get_info_from_line(line):
  colon = line.index(":")
  new_line = line[colon + 1:].strip()
  return new_line

if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument("-i", "--inspections", help="One or more inspections files from which to create the spreadsheet", nargs=argparse.ONE_OR_MORE, type=str, required=True)
  
  args = parser.parse_args()
  
  inspections = args.inspections
  
  main(inspections)