from z3 import *

# Exercise 7: Verify Store(A, i*i - i*i, x)[0]>=x

class Todo(Exception):
    pass

# We already discussed the problem
# Store(A, i*i - i*i, x)[0]>=x
# is undecidable because it contains non-linear arithmetic.
# Now try to convert it into a Z3 formulae and investigate the output.
# Whether it's "unknown" or not?
# What's the reason?

a = Array('a', IntSort(), IntSort())
x = Int('x')
i = Int('i')

def gen_formulae():
    """Fill your code here"""
    return Store( a, i*i - i*i, x)

def prove(P):
    print( Select(P,0) >= x)

if __name__ == '__main__':
    P = gen_formulae()
    prove(P)
    # It's print: Store(a, i*i - i*i, x)[0] >= x, not "unknown"
    # In my view, although i * i maybe exceed 2^31 - 1, but i * i equal i * i, so the result is not "unkonwn"
