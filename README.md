# Precis

## Requirements
1. Python version: 3.6 and pip
2. lxml --> pip install lxml
3. python z3 library

## Development notes
1. When executing this program in VSCode, relative paths used in our code depends on where you open VSCode.

## Instrumenter
1. Usage: Instrumenter.exe --solution=<> --project-name=<> --test-file-name=<> --PUT-name=<> --post-condition=<>
2. Note: solution needs to be path!
3. Example: Instrumenter.exe --solution=$your dir of Stack$/Stack/Stack.sln --test-project-name=StackTest --test-file-name=StackContractTest.cs --PUT-name=PUT_PushContract  --post-condition=true

## TODO:


## BUG List (fixed):
1. ***Data/feature_vector.py***: Why ```range(len(values) - 1)``` before?  
Before, values contains test label at the end, so the actual values don't include the last one. Now we have the constructor with additional field ```testLabel```, so it should be ```range(len(values))``` now. 

2. ***Teacher/houdini.py***: ```f.varZ3[i]``` out of range  
It comes from 1, if the input ```values``` are all actual values (without ```testLabel```) are we use ```range(len(values) - 1)```, then we will miss the value at the end. If we change it to ```range(len(values))``` we should be good.

3. ***Data/feature_vector.py***: ```valuesZ3``` should be ```False``` but print is ```True```  
Note!!! In z3py, ```BoolVal('False')``` returns ```True```, but ```BoolVal(False)``` returns ```False```. We should initialize with bool value rather than string.

4. ***Leaner/houdini.py***: ```substitute()``` doesn't work. The reason is that before ```PrecisFeature``` is initialized with string of variable name, which makes no sense for derived features such as ```New_Count != Old_Count```. Now, we added new field ```isDerived``` in constructor of ```PrecisFeature```, when ```isDerived``` is ```True```, we set ```PrecisFeature``` with a Z3 expression direcetly, if not then we use string of variable name and string of variable type to initialize the feature.