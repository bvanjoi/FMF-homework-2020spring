from z3 import *

class Todo(Exception):
    pass

x, y = BitVecs('x y', 32)

# Given two bit vectors, computer their multiplication, return two value:
# an overflow flag, and the result (after rounding).
# For instance, for x=1, y=2, return (False, 2).
# for x=0x80000000, y=2, return (True, 0)
def mult_with_overflow(x, y):
    '''
    add your implementation here:
    '''
    INT_MAX = 2**31-1
    if simplify(x >= 0) and simplify(y >= 0):
        if simplify((INT_MAX / x) < y):
            return True, 0
        else:
            return False, simplify(x * y)
    elif simplify(x<0) and simplify(y<0):
        if simplify((INT_MAX / x) > y):
            return True, 0
        else:
            return False, simplify(x * y)
    elif x * y == -2**32:
        return True, 0
    elif simplify(x < 0):
        return mult_with_overflow( simplify(x<<1>>1), y)
    else:
        return mult_with_overflow(x, simplify(y<<1>>1))
    

if __name__ == '__main__':
    # some unit tests
    x = BitVecVal(1, 32)
    y = BitVecVal(2, 32)
    of, res = mult_with_overflow(x, y)
    if not((not of) and res == 2):
        print("Wrong!")
    else:
        pass
    x = BitVecVal(0x80000000, 32)
    y = BitVecVal(2, 32)
    of, res = mult_with_overflow(x, y)
    # some unit tests
    if not (of and res == 0):
        print("Wrong!")
    else:
        pass

