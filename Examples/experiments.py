import inputCreatorNemo
import os
import time
import random
import json
import subprocess

ruleFile = "el-calc.rls"
folder = "/home/johannes/nemo-examples/examples/owl-el/from-preprocessed-csv"
outputformat = "-g"
tries = 5
atomsPerTry = 100

def singleTry():
    originalDir = os.getcwd()
    os.chdir(folder)

    model = inputCreatorNemo.getModel()

    os.chdir(originalDir)

    with open("log.txt", "a+") as log:
        for i in range(0,tries):
            log.write("---\n")
            atoms = []
            while len(atoms) < atomsPerTry:
                atom = random.choice(model)
                if atom not in atoms:
                    atoms.append(atom)
                #print(atoms)
            inputCreatorNemo.main(folder, ruleFile, outputformat, *atoms)

            print("Start")
            start = time.time()
            problemFile = ruleFile.split(".")[0] + ".json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            if outputformat == "-g":
                result = subprocess.run(["./build/bin/certifyingDatalog", outputformat, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
            else:
                result = subprocess.run(["./build/bin/certifyingDatalog", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            if outputformat == "-t":
                log.write(json.dumps({"trees": problem["trees"], "Result": result.stdout, "Time": str(duration)}, indent=4))
            elif outputformat == "-g":
                log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Time": str(duration)}, indent=4))
                

def multiTry():
    originalDir = os.getcwd()
    os.chdir(folder)

    model = inputCreatorNemo.getModel()

    os.chdir(originalDir)

    with open("log.txt", "a+") as log:
        for i in range(0,tries):
            # log.write("Try" + str(i) + "---\n")
            atoms = []
            while len(atoms) < atomsPerTry:
                atom = random.choice(model)
                if atom not in atoms:
                    atoms.append(atom)
                #print(atoms)
            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-t", *atoms)
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run(["./build/bin/certifyingDatalog", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            
            log.write(json.dumps({"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)}, indent=4))

            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-g", *atoms)
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run(["./build/bin/certifyingDatalog", "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start 
            
            log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)}, indent=4))


multiTry()
