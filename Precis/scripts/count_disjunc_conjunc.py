import argparse


def get_entry(line):
  colon = line.index(':')
  result = line[colon + 1:].strip()
  return result


def get_contract(lines:str):
  contract = ""
  put_name = ""
  smt_result = ""
  for line in lines:
    if "PUT_" in line:
      put_name = line.strip()
    if "smt check" in line:
      smt_result = get_entry(line)
    if "CNF simplified:" in line:
      contract = get_entry(line)
      
  return put_name, smt_result, contract


def extract_puts(lines:str):
  puts = lines.split("---------------------")
  return puts[1:]


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


def count(precis, daikon, check_precis_is_conjunctive):
  puts = []
  
  with open(precis) as pf:
    p_lines = "".join(pf.readlines())

  with open(daikon) as df:
    d_lines = "".join(df.readlines())
    
  p_puts = extract_puts(p_lines)
  d_puts = extract_puts(d_lines)

  p_puts = sort_puts(p_puts)
  d_puts = sort_puts(d_puts)

  assert(len(p_puts) == len(d_puts))

  for put_idx in range(len(p_puts)):
    p_put_lines = p_puts[put_idx].split('\n')
    d_put_lines = d_puts[put_idx].split('\n')
    
    p_put, p_smt, p_contract = get_contract(p_put_lines)
    d_put, d_smt, d_contract = get_contract(d_put_lines)
    
    p_is_conjunctive = is_conjunctive(p_contract)
    d_is_conjucntive = is_conjunctive(d_contract)
    
    if (check_precis_is_conjunctive and p_is_conjunctive and not d_is_conjucntive) or (not check_precis_is_conjunctive and not p_is_conjunctive and d_is_conjucntive):
      if 'Precis' in d_smt:
        puts.append(p_put)
        
  return puts


if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument('-p', '--precis', help="The precis inspection file", type=str)
  parser.add_argument('-d', '--daikon', help="The precis inspection file", type=str)
  parser.add_argument('-c', "--precis_conjunctive", help="stores if precis should be the conjunctive contract", action='store_true', default=False)

  args = parser.parse_args()

  precis = args.precis
  daikon = args.daikon
  precis_is_conjunctive = args.precis_conjunctive

  puts = count(precis, daikon, precis_is_conjunctive)
  
  if precis_is_conjunctive:
    print(f"Precis Con and Daikon Dis ({len(puts)}): {puts}")
  else:
    print(f"Precis Dis and Daikon Con ({len(puts)}): {puts}")