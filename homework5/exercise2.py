from z3 import *

# Before we presenting the EUF theory, we first introduce some Z3's
# facilities to define terms and functions.

########################################
# Sort, term, formula

# In Z3, we can define sorts, we can simply think them as sets.
# This code:
S = DeclareSort('S')
f = Function('f', S, S)
x1, x2, x3, x4, x5 = Consts('x1 x2 x3 x4 x5', S)
solve(x1 == x2, x2 == x3, x4 == x5, x5 != x1, f(x1) != f(x3))
# what's Z3's output? And why that output?


