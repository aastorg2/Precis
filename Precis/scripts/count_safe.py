import argparse


def count_truly_safe(inspection):
  with open(inspection) as f:
    lines = f.readlines()

  true_count = 0
  false_count = 0

  for line in lines:
    if "Truly Safe" in line:
      colon = line.index(':')
      result = line[colon:].strip()

      if "True" in result:
        true_count += 1
      elif "False" in result:
        false_count += 1
        
  return true_count, false_count

def count_strength(inspection):
  with open(inspection) as f:
    lines = f.readlines()

  precis_count = 0
  other_count = 0
  equivalent_count =0
  incomparable_count = 0

  for line in lines:
    if "smt check:" in line:
      colon = line.index(':')
      result = line[colon:].strip()

      if "Precis" in result:
        precis_count += 1
      elif "Daikon" in result or "Other" in result:
        other_count += 1
      elif "Unknown" in result or "Incomparable" in result:
        incomparable_count +=1
      elif "Equivalent" in result:
        equivalent_count +=1

  return precis_count, other_count, equivalent_count, incomparable_count


if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument("-i", "--inspection", help="The inspection file", type=str)
  parser.add_argument("-m", "--mode", help="safe: count safety, stren: count strength", type=str)
  args = parser.parse_args()

  inspection = args.inspection
  mode = args.mode

  if mode.upper() == "SAFE":
    num_true, num_false = count_truly_safe(inspection)
    print(f"Safe: {num_true}")
    print(f"Not Safe: {num_false}")
  elif mode.upper() == "STREN":
    precis, other, equiv, incomp = count_strength(inspection)
    print(f"Precis: {precis}")
    print(f"Other: {other}")
    print(f"Equivalent: {equiv}")
    print(f"Incomparable: {incomp}")
