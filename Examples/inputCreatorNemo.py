import json
import os
import re
import sys

def parseAtom(s):
    return s.replace("\"", "")

def getTree(object):
    children = []
    members = []
    if "premises" in object:
        for atom in object["premises"]:
            label = parseAtom(atom)
            children.append({"node": {"label": label, "children": []}})
            members.append(label)
    label = parseAtom(object["conclusion"])

    tree = {"node": {"label": label, "children": children}}
    members.append(label)
    return (tree, members)

def expandTree(tree1, tree2):
    currNode = tree1["node"]

    if currNode["label"] == tree2["node"]["label"]:
        return tree2
    
    newChildren = []

    for child in currNode["children"]:
        newChildren.append(expandTree(child, tree2))

    return {"node": {"label": currNode["label"],"children":  newChildren}}



def parseTree(json_object):
    getTreeResult = getTree(json_object["inferences"][0])
    tree = getTreeResult[0]
    members = set(getTreeResult[1])

    for i in range (1, len(json_object["inferences"])):
        getTreeResult = getTree(json_object["inferences"][i])
        tree = expandTree(tree, getTreeResult[0])
        for member in getTreeResult[1]:
            members.add(member)

    return (tree, member)

def getModel():
    model = []
    for filename in os.listdir("results"):
        with open("results/" + filename, "r") as f:
            filename = filename.split(".")[0]
            for line in f:
                if line != "":
                    line = line.replace("\n", "")
                    model.append(filename + "(" + line + ")")
    return model

def elementForCommandLine(s):
    result = re.match(r"(.+)\((.+)\)",s)
    newElements = []
    for element in result[2].split(","):
        newElements.append('\\\"' + element + "\\\"")

    return "\"" + result[1] + "(" + ",".join(newElements) +  ")" + "\""

    

def main(folder, ruleFile):
    print("Start")
    problemName = ruleFile.split(".")[0]
    originalDir = os.getcwd()
    os.chdir(folder)

    model = getModel()
    model2=set(model)
    trees = []

    while len(model2) > 0:
        element = model2.pop()
        os.system("nmo  --trace " + elementForCommandLine(element) + " --trace-output temp " + ruleFile)

        with open("temp") as f:
            parseTreeResult=parseTree(json.load(f))
            trees.append(parseTreeResult[0])

            model2.difference_update(parseTreeResult[1])
    
    os.chdir(originalDir)
    with open(problemName, "w") as f:
        json.dump({"model": model, "trees": trees}, f, ensure_ascii=False, indent=4)


if __name__ == "__main__":
    #main(sys.argv[1], sys.argv[2])
    main("/home/johannes/nemo/resources/testcases/johannes/test1", "program.rls")



    