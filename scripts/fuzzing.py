
#!/usr/bin/python
import sys, getopt
from z3 import *
import json
import random

print(sys.setrecursionlimit(1000))
COUNT = 0

def randoSMT(s, initial_terms,bound,count,flag):
    listTest = []
    COUNT = 0
    while(count < bound):
        if sat == s.check():
            m = s.model()
            # print("HERE ", m)
            for i in range(len(initial_terms)-1):
                block_term(s, m, initial_terms[i])
            listTest.append(m)
        else:
            return listTest
        count = count + 1
    return listTest

def block_term(s, m, t):
    s.add(t != m.eval(t, model_completion=True))


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



def runAndPrintSMTQueries(s,listOfVars,numOfTrials,rand):
    # m = randoSMT(s,listOfVars,numOfTrials,0,False)
    # for i in range(len(m)):
    #     print("Example RANDO (",i,") = ", m[i])
    try:
        if(rand):
            models = randoSMT(s,listOfVars,numOfTrials,0,False)
        else:
            models = list(all_smt(s,listOfVars,numOfTrials,0))
    except Exception as e:
        # print(e)
        msg,models = e.args
    for i in range(len(models)):
        print("Example (",i,") = ", models[i])
    if(len(models) == 0):
        print("\nNo Satisfying assingments with these constraints!")

def createAndRunSMTQueries(vals,query,numOfTrials,rand):
    listOfVars = []
    _g = globals()
    for v in vals:
        if(vals.get(v) == "Int"):
            temp = Int(str(v))
            _g[v] = Int(str(v))
            listOfVars.append(temp)
    print("Varaibles =",listOfVars)
    s = Solver()
    v = eval(query,_g)
    s.add(v)
    print("Constraints = ",s)
    runAndPrintSMTQueries(s,listOfVars,int(numOfTrials),rand)

    #MAX INT
    for var in listOfVars:
        s = Solver()
        v = eval(query,_g)
        s.add(v)
        print("\n====Testing MAX Values for: ", var,"======")
        s.add(var == sys.maxsize)
        print("Constraints = ",s)
        runAndPrintSMTQueries(s,listOfVars,2,rand)

    #MIN INT
    for var in listOfVars:
        s = Solver()
        v = eval(query,_g)
        s.add(v)
        print("\n====Testing MIN Values for: ", var,"======")
        s.add(var == -sys.maxsize-1)
        print("Constraints = ",s)
        runAndPrintSMTQueries(s,listOfVars,2,rand)

def usage():
    return ("fuzzing.py" + 
                    "\n\t -vals [dictionary of input type pairs] " +
                    "\n\t\t i.e:  '{ \"key1\": \"value 1\", \"key2\": \"value 2\" }' " + 
                    "\n\t -q <query> "+ 
                    "\n\t\t smt query i.e: \"And(c >= a, c >= b), Or(c == a, c == b)\"")

def main(argv):
    vals = {}
    query = ""
    numOfTrials = 0
    rand = False
    try:
        opts, args = getopt.getopt(argv,"hi:q:v:n:r:",["vals=","query=","numOfTrials=","rand="])
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
        elif opt in ("-r", "--rand"):
            rand = arg

    print("======================================")
    print('vals are: ', json.dumps(vals))
    print('query is: ', query)
    print('num of trials: ', numOfTrials)
    print('Rand: ', rand)
    print("======================================")
    createAndRunSMTQueries(vals,query,numOfTrials,rand) #ASSUMES ALL VAR ARE INT
    # for a in vals:
    #     print(vals.get(a))


if __name__ == "__main__":
   main(sys.argv[1:])


# python fuzzing.py -v '{ "a": "Int", "b": "Int" , "c":"Int"}'  -q "And(c >= a, c >= b)" -n 4




#### OLD ####
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