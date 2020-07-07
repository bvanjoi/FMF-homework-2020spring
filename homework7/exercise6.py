from z3 import *

# Exercise 6: to prove Store(A, i, x)[i]>=x

class Todo(Exception):
    pass

# First we define some basic var types
A = Array('A', IntSort(), IntSort())
x = Int('x')
i = Int('i')

# This function returns the above formulae:
# Store(A, i, x)[i]>=x
# Now you should fill in the definition of the above formulae:
def gen_formulae():
    """Fill your code here"""
    B = Store(A, i, x)
    return B

def prove(P):
    solve(Not(Select(P,i) >= x))

if __name__ == '__main__':
    P = gen_formulae()
    prove(P)
