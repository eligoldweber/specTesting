
from z3 import *
import sys

print(sys.setrecursionlimit(1000))
COUNT = 0


def all_smt(s, initial_terms):
    def block_term(s, m, t):
        # print("blocking : " + str(t != m.eval(t, model_completion=True)))
        s.add(t != m.eval(t, model_completion=True))
    def fix_term(s, m, t):
        # print("fixing : " + str(t == m.eval(t, model_completion=True)))
        s.add(t == m.eval(t, model_completion=True))
    def all_smt_rec(terms):
        global COUNT
        if sat == s.check():
           m = s.model()
           yield m
        #    print(m)
        #    print("here " + str(COUNT))
           COUNT = COUNT + 1
        #    if(COUNT == 1000):
        #     return None
           for i in range(len(terms)):
               s.push()
               block_term(s, m, terms[i])
               for j in range(i):
                   fix_term(s, m, terms[j])
               yield from all_smt_rec(terms[i:])
               s.pop()   

    yield from all_smt_rec(list(initial_terms))


x = Int('x')
y = Int('y')
s = Solver()
v = x + y < 10, x > 1, y > 1
s.add(v)
print(s.check())
print(s.model())

models = list(all_smt(s,[x,y]))
# print (len(models))
print ((models))

a = Int('a')
b = Int('b')
c = Int('c')
s = Solver()

s.add(And(c >= a, c >= b),a >= 0,a < 10,b >= 0,b < 10,c < 50)
vals = list(all_smt(s, [a, b,c]))[:100]

for i in range (len(vals)):
    print(""+str(i) + " :: " + str(vals[i]))
# print(vals)
# aVals = "["
# bVals = "["
# cVals = "["
# for x in vals:
#     aVals = aVals + str(x[a]) + ","
#     bVals = bVals + str(x[b]) + ","
#     cVals = cVals + str(x[c]) + ","
# print(aVals)
# print("---")
# print(bVals)
# print("---")
# print(cVals)
# print("---")
