from os import replace
from z3 import *

# exercise1
x, y = Ints('x y')
solve( 
    x + y >= 2,
    2*x - y >= 0, 
    -x + 2*y >=1)

# exercise2
x, y = Reals('x y')
solve( 
    x + y >= 0.8, 
    x + 5*y >= 0.2, 
    x + 3*y <= 0)