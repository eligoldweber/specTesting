#!/usr/bin/python
import sys, getopt
# ASSUMES PREDICATE IS IN THE FORM (With the body bracket on the next line after the parameters)
# PREDICATE NAME(PARAM1, PARAM2)
# {

# }
#works with predicates right now
def findFunctionInFile(in_filename,origFnName):
    fo = open(in_filename,"r+")
    dafnyCode = fo.readlines()
    count = 0
    listofLines = []
    foundStart = False
    # Look for a predicate
    fullFnName = "predicate "+ origFnName + "("
    for line in dafnyCode:
        args = line.split()
        if(foundStart and line.strip()):   
            listofLines.append(line.strip())
        else:
            foundStart = False
        if(fullFnName in line):
            listofLines.append(line.strip())
            foundStart = True
        count = count + 1
    if (listofLines == []):
        #could be a lemma!
        count = 0
        fullFnName = "lemma "+ origFnName + "("
        for line in dafnyCode:
            args = line.split()
            if(foundStart and line.strip()):   
                listofLines.append(line.strip())
            else:
                foundStart = False
            if(fullFnName in line):
                listofLines.append(line.strip())
                foundStart = True
            count = count + 1
    return listofLines

# returns:
# (fullparams) == String of new and old parameters
# (generatedPreConds) == List of strings, that are the new necessary pre conditions
def handleSMPredicateParamsAndPreCond(parameters,origFnName):
    #(ASSUME) 'next' state var is marked with " ' " notation
    # print(parameters)
    newParameters = []
    partialNewParams = []
    originalNextVar = []
    fullparams = ""

    for p in parameters:
        if ("'" in p):
            individualP = p.split(":")
            partialNewParams.append(individualP[0]+"':"+individualP[1])
            newParameters.append(individualP[0]+"':"+individualP[1])
            originalNextVar.append(p)
        else:
            partialNewParams.append(p)
     # put all params together
    for origP in parameters:
        fullparams = fullparams + origP + ","
    for newP in newParameters:
        fullparams = fullparams + newP + ","
    fullparams = fullparams[:-1]
    # generate template pre-conditions
    generatedPreConds = []
    generatedPreConds.append("requires " + origFnName + "(" + stripParameterTypes(parameters) + ")")
    generatedPreConds.append("requires " + origFnName + "(" + stripParameterTypes(partialNewParams) + ")")
    return fullparams,generatedPreConds, originalNextVar, newParameters

# returns:
# (fullparams) == String of new and old parameters
# (generatedPreConds) == List of strings, that are the new necessary pre conditions
# (oldParams) == List of original parameters
# (newParams) == List of new parameters
def handleNonSMPredicateParamsAndPreCond(parameters):
    newParameters = []
    fullparams = ""
    for p in parameters:
        individualP = p.split(":")
        newParameters.append(individualP[0]+"':"+individualP[1])            
    # put all params together
    for origP in parameters:
        fullparams = fullparams + origP + ","
    for newP in newParameters:
        fullparams = fullparams + newP + ","
    fullparams = fullparams[:-1]
    # generate template pre-conditions
    generatedPreConds = []
    for i in range(len(parameters)):
        gPreCond = "requires " + parameters[i].split(":")[0] + " == " + newParameters[i].split(":")[0]
        generatedPreConds.append(gPreCond)
    return fullparams, generatedPreConds ,parameters, newParameters

# returns:
# (existingPreCond) == List of exisiting Pre Conditions 
def handleExistingPreConditions(originalFn):
    #Assuming no 'ensures', existing Requires are between params and start of body
    indexOfBodyStart = originalFn.index("{")
    existingPreCond = originalFn[1:indexOfBodyStart]
    return existingPreCond

#returns
# (stripedParameters) == list of parameters stripped of their 'types'
def stripParameterTypes(parameterList):
    stripedParameters = ""
    for p in parameterList:
        stripedParameters = stripedParameters + p.split(":")[0] + ","
    return stripedParameters[:-1]

# returns:
# (fullparams) == String of new and old parameters
# (originalPreconds) == List of strings, that are the original pre conditions    
def handleLemmaParamsAndPreCond(parameters,originalFn):
    fullparams = ""
    for p in parameters:
        fullparams += p + ","
    fullparams = fullparams[:-1]
    originalPreconds = []
    for line in originalFn:
        if "requires" in line:
            originalPreconds.append(line)
    return fullparams,originalPreconds

# returns:
# (fullBody) == Generated body for lemma 
def generateLemmaBodyFromLemma(parameters,origFnName):
    # print(stripParameterTypes(parameters))
    fullBody = ("var result := " + origFnName + "(" + stripParameterTypes(parameters) + ");"
                + "\n\tvar result' := " + origFnName + "(" + stripParameterTypes(parameters) + ");"
                + "\n\tassert result == result';")
    return(fullBody)

# creates lemma as a String
def makeLemma(lemmaName,parameterList,preConds,postConds,body):
    lemma = "lemma " + lemmaName + "(" + parameterList + ")"
    for preC in preConds:
        lemma = lemma + "\n\t" + preC
    for postC in postConds:
        lemma = lemma + "\n\t" + postC
    lemma = lemma + "\n{\n\t" + body + "\n}"
    return lemma

def generateNDLemmaFromPredicate(originalFn,origFnName,isStateTransPredicate):
    lemmaName = "is_"+origFnName+"_ND"
    fullparams = ""
    generatedPreConds = []
    existingPreCond = []
    newPostCond = []
    #handle parameters
    parameters = originalFn[0].split("(")[1][:-1].split(",")
    # CASE: Normal Predicate
    if(not isStateTransPredicate):
        fullparams,generatedPreConds,origParams,newParams = handleNonSMPredicateParamsAndPreCond(parameters)
        #--handle existing pre-conditions--
        existingPreCond = handleExistingPreConditions(originalFn)
        # generate new post-condition
        newPostCond.append("ensures " + origFnName + "(" + stripParameterTypes(origParams) + ") == " + origFnName + "(" + stripParameterTypes(newParams) + ")")
    else:
        fullparams,generatedPreConds,originalNextVar, newParameters = handleSMPredicateParamsAndPreCond(parameters,origFnName)
        # print(fullparams)
         # generate new post-condition
        newPostCond.append("ensures " + originalNextVar[0].split(":")[0] + " == " + newParameters[0].split(":")[0])
    # put it all together
    return makeLemma(lemmaName,fullparams,existingPreCond+generatedPreConds,newPostCond,"")


def generateNDLemmaFromLemma(originalFn,origFnName,isStateTransPredicate):
    lemmaName = "is_"+origFnName+"_ND"
    fullparams = ""
    generatedPreConds = []
    existingPreCond = []
    newPostCond = []
    #handle parameters
    parameters = originalFn[0].split(")")[0].split("(")[1].split(",")
    fullparams,existingPreCond = handleLemmaParamsAndPreCond(parameters,originalFn)
    body = generateLemmaBodyFromLemma(parameters,origFnName)
    return makeLemma(lemmaName,fullparams,existingPreCond+generatedPreConds,newPostCond,body)

def usage():
    return ("nonDeterministicTestGenerator.py" +
                    "\n\t -h help " +
                    "\n\t -i <inputfile> " +
                    "\n\t -n <nameOfFunction> "+ 
                    "\n\t -s StateMachineFlag(default=False): " + 
                    "\n\t\t True: designated predicate is a state machine transition" + 
                    "\n\t\t False: designated predicate is a standard predicate"+
                    "\n\t -a AppendFlag(default=False): " + 
                    "\n\t\t True: generated lemma is appended to bottom of input file" + 
                    "\n\t\t False: generated lemma is only printed to console" )
def main(argv):
    inputfile = ''
    outputfile = ''
    nameOfFunction = ''
    smFlag = False
    appendFlag = False
    try:
        opts, args = getopt.getopt(argv,"hi:n:s:a:",["ifile=","noffun=","smFlag=","appendFlag="])
    except getopt.GetoptError:
        print(usage())
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print(usage())
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-n", "--noffun"):
            nameOfFunction = arg
        elif opt in ("-s", "--smFlag"):
            smFlag = arg
        elif opt in ("-a", "--appendFlag"):
            appendFlag = arg
    print("======================================")
    print('Input file is: ', inputfile)
    print('Name of Function to test is: ', nameOfFunction)
    print('StateMachineFlag: ', smFlag)
    print('AppendFlag: ', appendFlag)
    print("======================================\n")
    

    functionTxt = findFunctionInFile(inputfile,nameOfFunction)
    if(functionTxt[0].split()[0] == "predicate"):
        #generate ND test starting with a PREDICATE
        lemma = generateNDLemmaFromPredicate(functionTxt,nameOfFunction,smFlag)
    else:
        #generate ND test starting with a LEMMA
        lemma = generateNDLemmaFromLemma(functionTxt,nameOfFunction,smFlag)
    print(lemma)

    print("\n======================================\n")
    if(appendFlag):
        with open(inputfile, "a") as f:
            f.write("\n"+lemma)
        print("DONE: Appended to input file")
    else:
        print("DONE")

if __name__ == "__main__":
   main(sys.argv[1:])