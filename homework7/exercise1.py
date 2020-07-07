from z3 import *


class Todo(Exception):
    pass


x, y = BitVecs('x y', 32)
# Given two bit vectors, to compute their average:
def int_average(x, y):
    '''
    add your implementation here:
    pay attention:
        z3 中的 BitVec 是有符号的二进制数字
        for example:
        z = BitVec('z',2)
        solve(z == -1)  # [z=3]
        solve(z == 1)   # [z=1]
        因此要使用 LShR, 逻辑右移
    '''
    t = (x&y) + ((x^y)>>1)
    return t + (LShR(t,31) & (x^y))


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