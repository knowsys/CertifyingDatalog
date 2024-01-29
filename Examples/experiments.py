import inputCreatorNemo
import os
import time
import random
import json
import subprocess

ruleFile = "el-calc.rls"
folder = "/home/johannes/nemo-examples/examples/owl-el/from-preprocessed-csv"
tries = 100

originalDir = os.getcwd()
os.chdir(folder)

model = inputCreatorNemo.getModel()

os.chdir(originalDir)

with open("log.txt", "a+") as log:
    for i in range(0,tries):
        log.write("---\n")
        atom = random.choice(model)
        inputCreatorNemo.main(folder, ruleFile, atom)

        start = time.time()
        problemFile = ruleFile.split(".")[0]

        with open(problemFile) as file:
            problem = json.load(file)
            log.write(json.dumps(problem["trees"], ensure_ascii=False, indent=4))
            log.write("\n")

        result = subprocess.run(["./build/bin/certifyingDatalog", problemFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)

        log.write(result.stdout)
        duration = time.time() - start

        log.write(str(duration) + "\n")


        
