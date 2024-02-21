import inputCreatorNemo
import os
import time
import random
import json
import subprocess

ruleFile = "el-calc.rls"
folder = "/home/johannes/nemo-examples/examples/owl-el/from-preprocessed-csv"
outputformat = "-g"
tries = 1
atomsPerTry = 10000

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
        #inputCreatorNemo.main(folder, ruleFile, outputformat, *atoms)

        print("Start")
        start = time.time()
        problemFile = ruleFile.split(".")[0] + ".json"

        with open(problemFile) as file:
            problem = json.load(file)
        


        result = subprocess.run(["./build/bin/certifyingDatalog", outputformat, problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

        duration = time.time() - start
        if outputformat == "-t":
            log.write(json.dumps({"trees": problem["trees"], "Result": result.stdout, "Time": str(duration)}, indent=4))
        elif outputformat == "-g":
            log.write(json.dumps({"graph": problem["graph"], "Result": result.stdout, "Time": str(duration)}, indent=4))
            


        
