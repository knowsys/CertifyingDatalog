import inputCreatorNemo
import os
import time
import random
import json
import subprocess

ruleFile = "el-calc.rls"
folder = "./"
tries = 1
atomsPerTry = 1000

def multiTry():
    originalDir = os.getcwd()
    os.chdir(folder)

    model = inputCreatorNemo.getModel()

    print(model)

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
            
            problemFile = ruleFile.split(".")[0] + ".tree.json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run(["../../.lake/build/bin/certifyingDatalog", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start
            
            log.write(json.dumps({"trees": problem["trees"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)}, indent=4))

            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-g", *atoms)
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".graph.json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run(["../../.lake/build/bin/certifyingDatalog", "-g", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start 
            
            log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)}, indent=4))

            print("Start")
            start = time.time()
            inputCreatorNemo.main(folder, ruleFile, "-o", *atoms)
            
            preparation = time.time() - start
            
            problemFile = ruleFile.split(".")[0] + ".ograph.json"

            with open(problemFile) as file:
                problem = json.load(file)
            

            start = time.time()
            result = subprocess.run(["../../.lake/build/bin/certifyingDatalog", "-o", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

            duration = time.time() - start 
            
            log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Preparation time": str(preparation), "Validation time": str(duration)}, indent=4))


multiTry()
