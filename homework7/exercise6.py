from z3 import *

# Exercise 6: to prove Store(A, i, x)[i]>=x

class Todo(Exception):
    pass

# First we define some basic var types
A = Array('A', IntSort(), IntSort()) # A: f(Int) -> Int
x = Int('x')
i = Int('i')

# This function returns the above formulae:
# Store(A, i, x)[i]>=x
# Now you should fill in the definition of the above formulae:

# to be honset, the formulae must be right.
def gen_formulae():
    """Fill your code here"""
    return Store(A, i, x)

def prove(P):
    print( Select(P,i) >= x)
    return 
    
if __name__ == '__main__':
    P = gen_formulae()
    prove(P)