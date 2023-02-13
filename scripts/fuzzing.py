
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
           c = c + 1
           if(c >= bound):
             raise Exception("Current val at bound",listTest)
    
           for i in range(len(terms)):
               s.push()
               block_term(s, m, terms[i])
               for j in range(i):
                   fix_term(s, m, terms[j])
               yield from all_smt_rec(terms[i:],bound,c)
               s.pop()   

    yield from all_smt_rec(list(initial_terms),bound,count)


def runAndPrintSMTQueries(s,listOfVars,numOfTrials):
    try:
        models = list(all_smt(s,listOfVars,numOfTrials,0))
    except Exception as e:
        # print(e)
        msg,models = e.args
    for i in range(len(models)):
        print("Example (",i,") = ", models[i])
    if(len(models) == 0):
        print("\nNo Satisfying assingments with these constraints!")

def createAndRunSMTQueries(vals,query,numOfTrials):
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
    runAndPrintSMTQueries(s,listOfVars,int(numOfTrials))

    #MAX INT
    for var in listOfVars:
        s = Solver()
        v = eval(query,_g)
        s.add(v)
        print("\n====Testing MAX Values for: ", var,"======")
        s.add(var == sys.maxsize)
        print("Constraints = ",s)
        runAndPrintSMTQueries(s,listOfVars,2)

    #MIN INT
    for var in listOfVars:
        s = Solver()
        v = eval(query,_g)
        s.add(v)
        print("\n====Testing MIN Values for: ", var,"======")
        s.add(var == -sys.maxsize-1)
        print("Constraints = ",s)
        runAndPrintSMTQueries(s,listOfVars,2)

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
    createAndRunSMTQueries(vals,query,numOfTrials) #ASSUMES ALL VAR ARE INT
    # s = Solver()
    # I = IntSort()
    # A = Array('A', I, I)
    # i = Int("i")
    # f = Function('f', IntSort(), IntSort())
    # print(ForAll([i], f(i) == 0))
    # X = IntVector('x', 10)
    # Y = Array('y', IntSort(), IntSort())
    # solve(ForAll([i], i >= 0, i < 3, X[i] <= X[i+1]))
    # s.add(ForAll([i], X[i] <= X[i+1]))
    # print(s.check())
    # print(s.model())
    # solve(And(ForAll([i], X[i] <= X[i+1]),ForAll([i], Implies(i in X, i in Y))))
    # I = IntSort()
    # # A is an array from integer to integer
    # A = Array('A', I, I)
    # x = Int('x')
    # print(A[x])
    # print(Select(A, x))
    # print(Store(A, x, 10))
    # print(simplify(Select(Store(A, 2, x+1), 2)))
   
    # s = Solver()

    # f = Function('f', IntSort(), IntSort(),BoolSort())
    # x, y = Ints('x y')

    # a, b = Ints('a b')
    # f = Function('f', IntSort(), IntSort(), IntSort())
    # x, y = Ints('x y')
    # r = ForAll([x, y], And(f(x, y) == (x > y), x == 5))
    

    # solve(r)

if __name__ == "__main__":
   main(sys.argv[1:])


# python fuzzing.py -v '{ "a": "Int", "b": "Int" , "c":"Int"}'  -q "And(c >= a, c >= b)" -n 4