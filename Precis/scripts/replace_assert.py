import argparse

def main(test):
  
  with open(test) as f:
    lines = f.readlines()
    
  text = "".join(lines)
  
  new_text = text.replace('Assert.True', "PexAssert.IsTrue")
  
  with open(test, 'w') as f:
    f.write(new_text)
  

if __name__ == "__main__":
  parser = argparse.ArgumentParser()
  parser.add_argument("-t", "--test", help="The test file to perform replacement on", type=str)
  
  args = parser.parse_args()
  
  test = args.test
  
  main(test)