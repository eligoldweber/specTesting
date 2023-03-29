
#!/usr/bin/python
import sys, getopt
from z3 import *
import json
import random
import itertools

print(sys.setrecursionlimit(1000))
COUNT = 0


def blockAll(s):
    block = []
    m = s.model()
    for z3_decl in m: # FuncDeclRef
        arg_domains = []
        for i in range(z3_decl.arity()):
            domain, arg_domain = z3_decl.domain(i), []
            for j in range(domain.num_constructors()):
                arg_domain.append( domain.constructor(j) () )
            arg_domains.append(arg_domain)
        for args in itertools.product(*arg_domains):
            block.append(z3_decl(*args) != m.eval(z3_decl(*args)))
            # print(block)
    s.add(And(block))
 


def sortingEx(size):
    # Working on 10 elements
    SIZE = size

    # a is the original arary, sortedA will be the sorted version of it
    a       = IntVector('A', SIZE)
    sortedA = IntVector('S', SIZE)

    # Assert that sortedA is indeed sorted
    for i in range(SIZE-1):
        s.add(sortedA[i] <= sortedA[i+1])

    # convert them to bags:
    bagA = K(IntSort(), 0)
    bagS = K(IntSort(), 0)
    for i in range(SIZE):
        bagA = Store(bagA, a[i],       1 + Select(bagA, a[i]))
        bagS = Store(bagS, sortedA[i], 1 + Select(bagS, sortedA[i]))

    # assert that the bags are the same
    # s.add(bagA == bagS)

    # a few constraints to make output interesting. obviously you'll
    # have actual constraints, so these won't be needed
    if(SIZE > 8):
        # s.add(a[3] >= 1)    # a fixed element
        s.add(a[3] > a[4])  # out-of order

    # get and print the model
    r = s.check()
    if r == sat:
        m = s.model()
        finalA = []
        finalS = []
        for i in range(SIZE):
            finalA.append(m.evaluate(a[i],       model_completion=True))
            finalS.append(m.evaluate(sortedA[i], model_completion=True))
        print("SIZE = %s" % SIZE)
        print("Input = %s" % finalA)
        print("Sorted = %s" % finalS)
        print("-------")
    else:
        print("Solver said: %s" % r)

s = Solver()
for i in range(5):
    size = random.randint(0,10)
    sortingEx(size)
    blockAll(s)


