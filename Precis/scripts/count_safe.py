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


if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument("-i", "--inspection", help="The inspection file", type=str)

  args = parser.parse_args()

  inspection = args.inspection

  num_true, num_false = count_truly_safe(inspection)
  
  print(f"Safe: {num_true}")
  print(f"Not Safe: {num_false}")