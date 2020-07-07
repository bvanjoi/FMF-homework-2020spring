from z3 import *

class Todo(Exception):
    pass

x, y = BitVecs('x y', 32)

# Given two bit vectors, to compute their average:
def poc_of_overflow(x, y):
    solver = Solver()
    solver.add(x >=1, y == 4, x*y < 0)
    res = solver.check()
    if res == sat:
        print('found an poc for integer overflow: ', solver.model())
    else:
        print('success!')
    # 536870912 * 4 = 2147483647 = 2**31 > 2**31 - 1
if __name__ == '__main__':
    poc_of_overflow(x, y)