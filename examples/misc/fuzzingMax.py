
#!/usr/bin/python
import sys
from z3 import *

sys.setrecursionlimit(1000)

def fuzzMax():
    x = Int('x')
    y = Int('y')
    z = Int('z')
    s.push()
    s.add(z >= x)
    s.add(z >= y)
    s.add(z == x or z == y) # Comment me
    r = s.check()
    if r == sat:
        m = s.model()
        print("--------")
        tempx = m.evaluate(x, model_completion=True)
        tempy = m.evaluate(y, model_completion=True)
        tempz = m.evaluate(z, model_completion=True)
        print("x =", tempx)
        print("y =", tempy)
        print("z =", tempz)
        print("--------")
        s.pop()
        s.add(x != tempx)
        s.add(y != tempy)
        s.add(z != tempz)
    else:
        print("The spec is unrealistic")

s = Solver()

for i in range(100):
    fuzzMax()
