#!/usr/bin/python
import sys, getopt
from z3 import *
import json
import random

from itertools import permutations

print(sys.setrecursionlimit(1000))
COUNT = 0

def sortingEx(size, inpt, s):
    s.push()
    oupt = IntVector('o', size)

    for i in range(size - 1):
        s.add(oupt[i] <= oupt[i + 1])

    bagi = K(IntSort(), 0)
    bago = K(IntSort(), 0)

    for i in range(size):
        bagi = Store(bagi, inpt[i], 1 + bagi[inpt[i]])
        bago = Store(bago, oupt[i], 1 + bago[oupt[i]])
    s.add(bagi == bago)

    # get and print the model
    r = s.check()
    if r == sat:
        m = s.model()
        s.pop()
        finalo = []
        block = []
        for i in range(size):
            tempo = m.evaluate(oupt[i], model_completion=True)
            finalo.append(tempo)
            block.append(oupt[i] != tempo)
        s.add(Or(block))
        print("Sorted = %s" % finalo)
        print("-------")
        return True
    else:
        print("Solver said: %s" % r)
        return False

lower = 1
upper = 5
for size in range(1, 5):
    pers = list(permutations(range(1, size + 1)))
    for per in pers:
        for i in range(2):
            s = Solver()
            print(list(per))
            sortingEx(size, per, s)
