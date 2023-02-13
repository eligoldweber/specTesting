
from z3 import *
import sys
# from mpl_toolkits import mplot3d
import numpy as np
# import matplotlib.pyplot as plt

print(sys.setrecursionlimit(1000))

COUNT = 0
# count = 0


def fullMaxSpec(o):
    return And(o >= a, o >= b, Or(o == b, o == a))

def partialMaxSpec(o):
    return And(o >= a, o >= b)


def tooStrongMax(o):
    return And(o > a, o > b, Or(o == b, o == a))

def between(o):
    return And(o >= a, o <= b) 

def test_smt(s,initial_terms):
    def block_term(s, m, t):
        global COUNT
        print("blocking1 : "+ str(COUNT) + " " + str(t != m.eval(t, model_completion=True)))
        s.add(t != m.eval(t, model_completion=True))
        COUNT = COUNT + 1
        if(COUNT >= 2):
            return None
    def fix_term(s, m, t, i):
        for j in range(i):
            print("fixing : " + str(t[j] == m.eval(t[j], model_completion=True)))
            s.add(t[j] == m.eval(t[j], model_completion=True))
    def test_smt_rec(terms):
        # global COUNT
        if sat == s.check():
           m = s.model()
           yield m
           i = len(terms)-1
        #    for i in range(len(terms)):
           s.push()
           block_term(s, m, terms[i])
           fix_term(s, m, terms,i)
           yield from test_smt_rec(terms[i:])
           s.pop()   
        #    for j in range(i):
        #     fix_term(s, m, terms[j])
        #     yield from test_smt_rec(terms[i:])
        #     s.pop()   
    yield from test_smt_rec(list(initial_terms))


print ("--Random Spec--")

x = Int('x')
y = Int('y')
s = Solver()
v = x + y < 10, x > 1, y > 1
s.add(v)
print(s.check())
print(s.model())
# simple Test

terms = [x,y]

m = s.model()
s_diff = Solver()
s_diff.add(v)
for i in range(len(terms)-1):
    print ("fixing (input) = " + str(terms[i]))
    s_diff.add(terms[i] == m.eval(terms[i], model_completion=True)) #ask input to be the same
print ("blocking previous result for = " + str(terms[len(terms)-1]))
s_diff.add(terms[len(terms)-1] != m.eval(terms[len(terms)-1], model_completion=True)) #ask output to be different
check = s_diff.check()
print(check)
if (check == sat):
    print(s_diff.model())
else:
    print("unsat")
# models = list(test_smt(s,[x,y]))
# print (len(models))
# print ((models))

print ("--Incomplete Max Spec--")


a = Int('a')
b = Int('b')
c = Int('c')
s = Solver()
v = And(c >= a, c >= b)
# s.add(a == 6)
s.add(v)
print(s.check())
print(s.model())

terms = [a,b,c]
m = s.model()
s_diff = Solver()
s_diff.add(v)
for i in range(len(terms)-1):
    print ("fixing (input) = " + str(terms[i]))
    s_diff.add(terms[i] == m.eval(terms[i], model_completion=True)) #ask input to be the same
print ("blocking previous result for = " + str(terms[len(terms)-1]))
s_diff.add(terms[len(terms)-1] != m.eval(terms[len(terms)-1], model_completion=True)) #ask output to be different
check = s_diff.check()
print(check)
if (check == sat):
    print(s_diff.model())
else:
    print("unsat")


print ("--Complete Max Spec--")


a = Int('a')
b = Int('b')
c = Int('c')
s = Solver()
v = And(c >= a, c >= b, Or(c == b, c == a))
s.add(v)
print(s.check())
print(s.model())

terms = [a,b,c]
m = s.model()
s_diff = Solver()
s_diff.add(v)
for i in range(len(terms)-1):
    print ("fixing (input) = " + str(terms[i]))
    s_diff.add(terms[i] == m.eval(terms[i], model_completion=True)) #ask input to be the same
print ("blocking previous result for = " + str(terms[len(terms)-1]))
s_diff.add(terms[len(terms)-1] != m.eval(terms[len(terms)-1], model_completion=True)) #ask output to be different
check = s_diff.check()
print(check)
if (check == sat):
    print(s_diff.model())
else:
    print("unsat")


print ("--test full--")

a = Int('a')
b = Int('b')
c = Int('c')
d = Int('d')
s = Solver()

s.add(fullMaxSpec(c))
s.add(d != c)
s.add(fullMaxSpec(d)) 

check = s.check()
print(check)
if (check == sat):
    print(s.model())
else:
    print("unsat")


print ("--test partial--")

a = Int('a')
b = Int('b')
c = Int('c')
d = Int('d')
s = Solver()

s.add(And(c >= a, c >= b))
s.add(d != c)
s.add(And(d >= a, d >= b))

s.add(partialMaxSpec(c))
s.add(d != c)
s.add(partialMaxSpec(d)) 

check = s.check()
print(check)
if (check == sat):
    print(s.model())
else:
    print("unsat")


print ("--test full--")

a = Int('a') 
b = Int('b')
c = Int('c')
d = Int('d')
s = Solver()


s.add(fullMaxSpec(c))
s.add(d != c)
s.add(fullMaxSpec(d)) 

check = s.check()
print(check)
if (check == sat):
    print(s.model())
else:
    print("unsat")


print ("--test too strong--")

a = Int('a')
b = Int('b')
c = Int('c')
d = Int('d')
s = Solver()

s.add(tooStrongMax(c))
# s.add(d != c)
# s.add(partialMaxSpec(d)) 

check = s.check()
print(check)
if (check == sat):
    print(s.model())
else:
    print("unsat")

# print ("--Sort Spec--")

# s = Solver()

# # Use I as an alias for IntSort()
# I = IntSort()
# # A is an array from integer to integer
# A = Array('A', I, I)
# B = Array('B', I, I)

# length = Int('length')
# x = Int('x')
# y = Int('y')
# print (A[x])
# # print (Select(A, x))
# # print (Store(A, x, 10))
# # print (simplify(Select(Store(A, 2, x+1), 2)))

# # s.add(And(A[0] > 10,A[1] < A[0],A[2] < A[1],A[2]> 0))
# v = ForAll(x,Implies(And(x >= 0, x < (length - 1) ),And(B[x] <= B[x+1])))
# vv = ForAll(x,Implies(And(x >= 0, x < length),Exists (y,A[y] == B[x])))
# greaterThanZero = length > 2
# s.add(greaterThanZero)
# s.add(v)
# s.add(vv)
# s.add(B[0] <= B[1])
# print(s.check())
# print(s.model())