
#!/usr/bin/python
import sys, getopt
from z3 import *
import json
import random
import itertools

print(sys.setrecursionlimit(1000))
COUNT = 0

def block_term(s, m, t):
    s.add(t != m.eval(t, model_completion=True))


def blockAll(s):
    block = []
    m = s.model()
    # print(m)
    for z3_decl in m: # FuncDeclRef
        arg_domains = []
        for i in range(z3_decl.arity()):
            domain, arg_domain = z3_decl.domain(i), []
            for j in range(domain.num_constructors()):
                arg_domain.append( domain.constructor(j) () )
            arg_domains.append(arg_domain)
        for args in itertools.product(*arg_domains):
            block.append(z3_decl(*args) != m.eval(z3_decl(*args)))
    s.add(And(block))
 
    # predicate GInv() 
    #     reads this`totalAmount, this`balances
    # {
    #     totalAmount == sum(balances)
    # }
    # function sum(m: map<int, int>): int
    # ensures sum(map[]) == 0


def tokenEx(size,c,num):
    SIZE = size
    K = IntVector('k', SIZE)
    X = IntVector('x', SIZE)
    s.add(c >= 0)
    if(SIZE == 0):
        s.push()
        s.add(Sum(X) == 0)
        s.add(c == 0)
        # print(s)
    else:
        s.push()
        sumWrong = 0
        for i in range(size):
            sumWrong += 42
        s.add(c == sumWrong)
        # s.add(Sum(X) == c)

    print("====")
    r = s.check()
    if r == sat:
        m = s.model()
        finalX = []
        s.pop()
        s.push()
        for i in range(SIZE):
            finalX.append(m.evaluate(X[i],model_completion=True))
            block_term(s,m,X[i])
        print("lemma fuzzingWrong_%s(){" % num)
        print("// SIZE = %s" % SIZE)
        print("var totalAmount := %s;" % m.evaluate(c))
        print("var i := %s;" % finalX)        
        print("assert Spec(totalAmount,i);\n}")
    else:
        print("HERE")
        # print(s)

s = Solver()
c= Int('c')
for i in range(100):
    # print("PRE")
    # print(s)
    # s.push()
    size = random.randint(0,20)
    tokenEx(size,c,i)
    # s.pop()
    # print("POST")
    # print(s)
    # blockAll(s)
