import argparse
from os import spawnl


def extract_puts(lines:str):
  puts = lines.split("---------------------")
  return puts[0], puts[1:]


def get_entry(line):
  colon = line.index(':')
  result = line[colon + 1:].strip()
  return result


def get_smt_status(lines:str):
  put_name = ""
  smt_result = ""
  safety_result = ""
  for line in lines:
    if "PUT_" in line:
      put_name = line.strip()
    elif "smt check" in line:
      smt_result = get_entry(line)
    elif "Truly Safe" in line:
      safety_result = get_entry(line)
      
  return put_name, smt_result, safety_result


def get_contract(lines:str):
  contract = ""
  for line in lines:
    if "CNF simplified:" in line:
      contract = get_entry(line)
      
  return contract


def insert_safety_result(lines:str, result:str):
  for line_idx in range(len(lines)):
    if "Truly Safe" in lines[line_idx]:
      line = lines[line_idx]
      colon = line.index(':')
      line = line[:colon + 1] + f" {result}"
      lines[line_idx] = line
      
  return lines


def alphabetical(l):
  return l[1]


def sort_puts(puts):
  for put_idx in range(len(puts)):
    puts[put_idx] = puts[put_idx].split('\n')
    
  sorted_puts=sorted(puts, key=alphabetical)
    
  for put_idx in range(len(sorted_puts)):
    sorted_puts[put_idx] = "\n".join(sorted_puts[put_idx])
  
  return sorted_puts


def is_conjunctive(contract:str):
  return not "||" in contract
  
  
def compare(precis:str, daikon:str):
  
  puts = []
  
  with open(precis) as pf:
    p_lines = "".join(pf.readlines())

  with open(daikon) as df:
    d_lines = "".join(df.readlines())
  
  p_heading, p_puts = extract_puts(p_lines)
  d_heading, d_puts = extract_puts(d_lines)
  
  p_puts = sort_puts(p_puts)
  d_puts = sort_puts(d_puts)
  
  # Inspections should have same number of puts
  assert(len(p_puts) == len(d_puts))
  
  for put_idx in range(len(p_puts)):
    p_put_lines = p_puts[put_idx].split('\n')
    p_put, p_smt, p_safety = get_smt_status(p_put_lines)
    
    if p_smt == "Precis":
      d_put_lines = d_puts[put_idx].split('\n')
      p_contract = get_contract(p_put_lines)
      d_contract = get_contract(d_put_lines)
      
      p_is_conjunctive = is_conjunctive(p_contract)
      d_is_conjucntive = is_conjunctive(d_contract)
      
      if p_is_conjunctive == d_is_conjucntive:
        puts.append(p_put)
      
  return puts
  
    
if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument('-p', '--precis', help="The precis inspection file", type=str)
  parser.add_argument('-d', '--daikon', help="The precis inspection file", type=str)
  
  args = parser.parse_args()
  
  precis = args.precis
  daikon = args.daikon
  
  puts = compare(precis, daikon)
  
  print(puts)