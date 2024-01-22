import json
import os
import re

def normalizeQuotationmarks(s):
    return ''.join(s.replace("\"", "").split())


def getTree(object):
    children = []
    if "premises" in object:
        for atom in object["premises"]:
            label = normalizeQuotationmarks(atom)
            children.append({"node": {"label": label, "children": []}})
    label = normalizeQuotationmarks(object["conclusion"])

    tree = {"node": {"label": label, "children": children}}
    return tree

def expandTree(tree1, tree2):
    currNode = tree1["node"]

    if currNode["label"] == tree2["node"]["label"]:
        return tree2
    
    newChildren = []

    for child in currNode["children"]:
        newChildren.append(expandTree(child, tree2))

    return {"node": {"label": currNode["label"],"children":  newChildren}}



def parseTrees(json_object):
    trees = []
    for atom in json_object["finalConclusion"]:
        trees.append({"node": {"label": normalizeQuotationmarks(atom), "children": []}})

    for i in range (0, len(json_object["inferences"])):
        getTreeResult = getTree(json_object["inferences"][i])

        newTrees = []
        for tree in trees:
            newTree = expandTree(tree, getTreeResult)
            newTrees.append(newTree)
        trees = newTrees        

    return trees

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

    return result[1] + "(" + ",".join(newElements) +  ")"

def tokenize(line):
    currToken = ""
    tokens = []

    for symbol in line:
        if symbol == "(" or symbol == ")":
            if currToken == "":
                tokens.append(symbol)
            else:
                tokens.append(currToken)
                currToken = ""
                tokens.append(symbol)
        elif symbol == "," or symbol == " ":
            if currToken == "":
                continue
            tokens.append(currToken)
            currToken = ""
        else:
            currToken = currToken + symbol

    return tokens

def convertNemoAtomToJson(tokens):
    symbol = tokens.pop(0)
    terms = []
    for token in tokens:
        if token == "(" or token == ")":
            continue
        if token.startswith("?"):
            terms.append({"variable": token})
        else:
            terms.append({"constant": token})
    
    return {"symbol": symbol, "terms": terms}

def convertListNemoAtomsToJson(tokens):
    stack = []
    atoms = []
    for token in tokens:
        if token == ")":
            stack.append(")")
            atoms.append(convertNemoAtomToJson(stack))
            stack = []
        else:
            stack.append(token)
    return atoms

def convertNemoProgramToJson(lines):
    transformedLines = []
    for line in lines:
        line = normalizeQuotationmarks(line)
        if line.startswith("@") or len(line.split()) == 0: # no lines with just white spaces or starting with @
            continue
        ruleSplit = line.split(":-")

        if len(ruleSplit) == 1:
            tokens = tokenize(line)
            transformedLines.append({"head": convertNemoAtomToJson(tokens), "body": []})
        else:
            head = convertNemoAtomToJson(tokenize(ruleSplit[0]))

            body = convertListNemoAtomsToJson(tokenize(ruleSplit[1]))
            transformedLines.append({"head": head, "body": body})
    return transformedLines

def convertNemoTreeAtomsToJson(tree):
    newLabel = convertNemoAtomToJson(tokenize(tree["node"]["label"]))
    
    newChildren = []
    for child in tree["node"]["children"]:
        newChildren.append(convertNemoTreeAtomsToJson(child))
    
    return {"node": {"label": newLabel, "children": newChildren}}

def treeMembers(tree):
    members = set()

    members.add(tree["node"]["label"])

    for child in tree["node"]["children"]:
        members.update(treeMembers(child))
    
    return members

def filterTrees(treeList):
    model = set()
    filteredTrees = []

    for tree in treeList:
        if tree["node"]["label"] in model:
            continue
        else:
            filteredTrees.append(convertNemoTreeAtomsToJson(tree))
            model.update(treeMembers(tree))

    return filteredTrees

def callExplain(goal, ruleFile):
    # print("Called "+ "nmo  --trace \"" + goal + "\" --trace-output temp " + ruleFile)
    os.system("nmo  --trace \"" + goal + "\" --trace-output temp " + ruleFile)
    trees = []
    with open("temp") as f:
        trees = (parseTrees(json.load(f)))

    return trees

def main(*args):
    complete = False
    if len(args) == 0:
        print("Empty input")
        return
    else:
        if args[0] == "--help" or args[0] == "-h":
            print("First input: path to folder where the data and results are stored")
            print("Second input: program file name, stored at the path above")
            print("Additional inputs may be ground atoms which should be tested")
            print("If no additional arguments are added, then the program will grab everything from the results folder and ask for trees for them.")
            return
        if len(args) == 2:
            complete = True
            ruleFile = args[1]
            folder = args[0]
        else:
            folder = args.pop(0)
            ruleFile = args.pop(0)

            model = args


    problemName = ruleFile.split(".")[0]
    originalDir = os.getcwd()
    os.chdir(folder)

    if complete:
        model = getModel()
    
    trees = []
    goal = ""
    for atom in model:
        if len(goal) > 20000:
            goal = goal.removesuffix(";")
            trees.extend(callExplain(goal, ruleFile))
            goal = elementForCommandLine(atom) + ";"

        else:
            goal = goal + elementForCommandLine(atom) + ";"
    goal = goal.removesuffix(";")
    trees.extend(callExplain(goal, ruleFile))
    trees = filterTrees(trees)
    
    program = []
    with open(ruleFile, "r") as file:
        program = convertNemoProgramToJson(file.readlines())

    os.chdir(originalDir)
    with open(problemName, "w") as f:
        json.dump({"trees": trees, "program": program}, f, ensure_ascii=False, indent=4)


if __name__ == "__main__":
    import sys
    #main(*sys.argv[1:])
    main("/home/johannes/nemo/resources/testcases/johannes/test1", "program.rls")



    