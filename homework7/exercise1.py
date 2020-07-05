from z3 import *

class Todo(Exception):
    pass

x, y = BitVecs('x y', 32)

# Given two bit vectors, to compute their average:
def int_average(x, y):
    '''
    add your implementation here:
    '''
    t = (x&y)+((x^y)>>1)
    return t + ( LShR(t,31) & (x^y))    
    # 需要注意的是 无符号右移

# we've given this correct implementation for you, but this is a
# special hack, you should not copy this code as your implementation.
def int_average_correct(x, y):
    ex = SignExt(1, x)
    ey = SignExt(1, y)
    result_correct = (ex+ey)/2
    return Extract(31, 0, result_correct)

if __name__ == '__main__':
    result1 = int_average(x, y)
    result2 = int_average_correct(x, y)
    solver = Solver()
    solver.add()
    res = solver.check(result1 != result2)
    if res == sat:
        print("Failed: your implementation is wrong!")
        m = solver.model()
        print('The counter example is: ', m)
    else:
        print('Exercise 1: Success!')






