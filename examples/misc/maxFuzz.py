from z3 import *

a = Int('a')
b = Int('b')
c = Int('c')

s = Solver()
s.add(c >= a)
s.add(c >= b)

for i in range(3):
    res = s.check()
    if res == sat:
        m = s.model()
        print("%d th iteration:" % (i + 1))
        print("a = ", m.evaluate(a))
        print("b = ", m.evaluate(b))
        print("c = ", m.evaluate(c))
        s.add(a == m.evaluate(a))
        s.add(Or(b != m.evaluate(b), c != m.evaluate(c)))

    
    