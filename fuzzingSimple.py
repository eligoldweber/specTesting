
#!/usr/bin/python
import sys, getopt
from z3 import *
import json

print(sys.setrecursionlimit(1000))
COUNT = 0




def all_smt(s, initial_terms,bound,count):
    listTest = []
    COUNT = 0
    def block_term(s, m, t):
        # print("blocking : " + str(t != m.eval(t, model_completion=True)))
        s.add(t != m.eval(t, model_completion=True))
    def fix_term(s, m, t):
        # print("fixing : " + str(t == m.eval(t, model_completion=True)))
        s.add(t == m.eval(t, model_completion=True))
    def all_smt_rec(terms,bound,c):
        global COUNT
        if sat == s.check():
           m = s.model()
           yield m
           listTest.append(m)
        #    print("M == " ,listTest)
        #    print("here " + str(c))
           c = c + 1
           if(c >= bound):
             raise Exception("Current val at bound",listTest)
    
           for i in range(len(terms)):
            #    print(i)
               s.push()
               block_term(s, m, terms[i])
            #    print("afterBlock")
               for j in range(i):
                   fix_term(s, m, terms[j])
            #    print("TERMS = " , terms[i:])
            #    print("S == ", s)
               yield from all_smt_rec(terms[i:],bound,c)
            #    print("S POP !! == ", s)
               s.pop()   

    yield from all_smt_rec(list(initial_terms),bound,count)


x = Int('x')
y = Int('y')
s = Solver()
# v = x + y < 10, x > 1, y > 1
v = x + y < 10

s.add(v)
# print(s.check())
# print(s.model())
try:
    models = list(all_smt(s,[x,y],4,0))
except Exception as e:
    # print(e)
    msg,models = e.args

print (len(models))
for m in models:
    print(m)
print ((models))

print("++++++")
x = Int('x')
y = Int('y')
s = Solver()
v =  eval("x + y < 10, x > 1, y > 1")
print(v)
s.add(v)
# print(s.check())
# print(s.model())

# models = list(bounded_smt_rec(s,[x,y],10))
# print (len(models))
# print ((models))

a = Int('a')
b = Int('b')
c = Int('c')
s = Solver()

# s.add(And(c >= a, c >= b),a >= 0,a < 10,b >= 0,b < 10,c < 50)
s.add(And(c >= a, c >= b), Or(c == a, c == b))
# print simplify(And(c >= a, c >= b), Or(c == a, c == b))
# s.add(And(c >= a, c >= b),a >= 0,a < 10,b >= 0,b < 10,c < 50)

# vals = list(all_smt(s, [a, b,c]))
try:
    models = list(all_smt(s,[a,b,c],10,0))
except Exception as e:
    print(e)
    msg,models = e.args

# print (len(models))
for m in models:
    print(m)


x = Int('x')
y = Int('y')
n = x + y >= 3
print("num args: ", n.num_args())
print("children: ", n.children())
print("1st child:", n.arg(0))
print("2nd child:", n.arg(1))
print("operator: ", n.decl())
print("op name:  ", n.decl().name())

listofVars = ["a"]
_a = locals()
for v in listofVars:
    _a[v] = Int(str(v))
    print( _a[v])
# f = Function('f', IntSort(), IntSort(), IntSort())
# /////
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

#returns
# (parameterMap) == map of parameters to their
def stripParameterTypes(parameterList):
    parameterMap = {}
    for p in parameterList:
        splitP = p.split(":")
        parameterMap[splitP[0]] = splitP[1]
    return(parameterMap)

def parsePredicateBody(functionTxt):
    body = functionTxt[2:-1]
    
    print(body)

def createSMTQuery(vals,query,numOfTrials):
    listofVars = []
    _g = globals()
    for v in vals:
        if(vals.get(v) == "Int"):
            temp = Int(str(v))
            listofVars.append(temp)
    print(listofVars) 
    s = Solver()
    v =  eval(query)
    s.add(v)

    try:
        models = list(all_smt(s,[a,b,c],int(numOfTrials),0))
    except Exception as e:
    # print(e)
        msg,models = e.args
    for m in models:
        print(m)
    #MAX
    for var in listofVars:
        s = Solver()
        v =  eval(query)
        s.add(v)
        print("====Testing MAX Values for: ", var,"======")
        s.add(var == sys.maxsize)
        print(s)
        try:
            models = list(all_smt(s,listofVars,2,0))
        except Exception as e:
            msg,models = e.args
        for m in models:
            print(m)
    #MIN
    for var in listofVars:
        s = Solver()
        v =  eval(query)
        s.add(v)
        print("====Testing MIN Values for: ", var,"======")
        s.add(var == -sys.maxsize-1)
        print(s)
        try:
            models = list(all_smt(s,listofVars,2,0))
        except Exception as e:
            msg,models = e.args
        for m in models:
            print(m)


def usage():
    return ("fuzzing.py" + 
                    "\n\t -vals [dictionary of input type pairs] " +
                    "\n\t\t i.e:  '{ \"key1\": \"value 1\", \"key2\": \"value 2\" }' " + 
                    "\n\t -q <query> "+ 
                    "\n\t\t smt query i.e: \"And(c >= a, c >= b), Or(c == a, c == b)\"")
def maxTest(a, b, c):
    val: bool = False
    val = ((c) > (a)) and ((c) > (b))
    return val


def main(argv):
    vals = {}
    query = ""
    numOfTrials = 0
    try:
        opts, args = getopt.getopt(argv,"hi:q:v:n:",["vals=","query=","numOfTrials="])
    except getopt.GetoptError:
        print(usage())
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print(usage())
            sys.exit()
        elif opt in ("-v", "--vals"):
            vals = json.loads(arg)
        elif opt in ("-q", "--query"):
            query = arg
        elif opt in ("-n", "--numOfTrials"):
            numOfTrials = arg

    print("======================================")
    print('vals are: ', json.dumps(vals))
    print('query is: ', query)
    print('num of trials: ', numOfTrials)
    print("======================================")
    createSMTQuery(vals,query,numOfTrials) #ASSUMES ALL VAR ARE INT
    # for a in vals:
    #     print(vals.get(a))


if __name__ == "__main__":
   main(sys.argv[1:])


# def main(argv):
#     inputfile = ''
#     nameOfFunction = ''
#     smFlag = False
#     try:
#         opts, args = getopt.getopt(argv,"hi:n:s:",["ifile=","noffun=","smFlag="])
#     except getopt.GetoptError:
#         print(usage())
#         sys.exit(2)
#     for opt, arg in opts:
#         if opt == '-h':
#             print(usage())
#             sys.exit()
#         elif opt in ("-i", "--ifile"):
#             inputfile = arg
#         elif opt in ("-n", "--noffun"):
#             nameOfFunction = arg
#         elif opt in ("-s", "--smFlag"):
#             smFlag = arg
#     print("======================================")
#     print('Input file is: ', inputfile)
#     print('Name of Function to test is: ', nameOfFunction)
#     print('StateMachineFlag: ', smFlag)
#     print("======================================\n")
    
#     functionTxt = findFunctionInFile(inputfile,nameOfFunction)
#     print(functionTxt)
#     if(functionTxt[0].split()[0] == "predicate"):
#         parameters = functionTxt[0].split("(")[1][:-1].split(",")
#         pMap = stripParameterTypes(parameters)
#         print(pMap)
#         parsePredicateBody(functionTxt)
#         print(maxTest(1,2,3))
#     else:
#         print("INPUT not correct")
#     print("DONE")

# ASSUME THAT INPUT IS PREDICATE IN FORM:

# Predicate Name(parameters)
# {
#     && (clause || clause) 
#     && clause
#     || clause
# }
# // === OLD iterative trial

# def bounded_block_term(s, m, t):
#         print("blocking : " + str(t != m.eval(t, model_completion=True)))
#         s.add(t != m.eval(t, model_completion=True))

# def bounded_fix_term(s, m, t):
#         print("fixing : " + str(t == m.eval(t, model_completion=True)))
#         s.add(t == m.eval(t, model_completion=True))

# def bounded_smt_rec(s,terms,bound):
#     listOfSmtResults = []
#     if sat == s.check():
#            m = s.model()
#            listOfSmtResults.append(m)
#            i = 0
#            while(len(listOfSmtResults) < bound):
#             print("i  = " + str(i) + " :: " + str(s))
#             if(i >= len(terms)):
#                 # i = 0
#                 return  listOfSmtResults
#                 # terms = terms[1:]
#             print("i  = " + str(i) + " :: " + str(terms))

#             s.push()
#             bounded_block_term(s, m, terms[i])
#             for j in range(i):
#                 bounded_fix_term(s, m, terms[j])
#             if sat == s.check():
#                 m = s.model()
#                 listOfSmtResults.append(m)
#                 print("ERE " + str(m) + "len = " + str(len(listOfSmtResults)))
#                 print(s)
                
#             else:
#                 print("inc I")
#                 s.pop()
#                 i += 1
#            return  listOfSmtResults

# def bounded_smt_rec_v2(s,terms,bound,listOfSmtResults):
#     i = 0
#     termIndex = 0
#     pushCount = 1
#     while(len(listOfSmtResults) < bound and termIndex < len(terms)):
#         if sat == s.check():
#             m = s.model()
#             listOfSmtResults.append(m)
#             # for i in range(len(terms)):
#             s.push()
#             bounded_block_term(s, m, terms[termIndex])
#             for j in range(termIndex):
#                 bounded_fix_term(s, m, terms[j])
#             # listOfSmtResults.append(bounded_smt_rec_v2(s,terms[termIndex:],bound,listOfSmtResults))
#         else:
#             # print("HERE == ", s)
#             for popCount in range(pushCount):
#                 s.pop()
#             pushCount += 1
#             termIndex += 1
#             i += 1
#     return listOfSmtResults



# ////
# x = Int('x')
# y = Int('y')
# s = Solver()
# # v = x + y < 10, x > 1, y > 1
# v = x + y < 10

# s.add(v)
# # print(s.check())
# # print(s.model())
# try:
#     models = list(all_smt(s,[x,y],4,0))
# except Exception as e:
#     # print(e)
#     msg,models = e.args

# print (len(models))
# for m in models:
#     print(m)
# print ((models))

# print("++++++")
# x = Int('x')
# y = Int('y')
# s = Solver()
# v =  eval("x + y < 10, x > 1, y > 1")
# print(v)
# s.add(v)
# # print(s.check())
# # print(s.model())

# # models = list(bounded_smt_rec(s,[x,y],10))
# # print (len(models))
# # print ((models))

# a = Int('a')
# b = Int('b')
# c = Int('c')
# s = Solver()

# # s.add(And(c >= a, c >= b),a >= 0,a < 10,b >= 0,b < 10,c < 50)
# s.add(And(c >= a, c >= b), Or(c == a, c == b))
# # print simplify(And(c >= a, c >= b), Or(c == a, c == b))
# # s.add(And(c >= a, c >= b),a >= 0,a < 10,b >= 0,b < 10,c < 50)

# # vals = list(all_smt(s, [a, b,c]))
# try:
#     models = list(all_smt(s,[a,b,c],10,0))
# except Exception as e:
#     print(e)
#     msg,models = e.args

# # print (len(models))
# for m in models:
#     print(m)


# c = Int('c')
# v = Int('v')
# w = Int('w')
# s = Solver()

# v = eval("And(v >= 0, v <= c, v > 0, w == v - 1)")
# print("!!!!!! = " ,v)

# s.add(v)
# print(s.check())
# print(s.model())
# print(s.check())
# print(s.model())
# listOfVars = ["a"]
# _a = locals()
# for v in listOfVars:
#     _a[v] = Int(str(v))
#     print( _a[v])