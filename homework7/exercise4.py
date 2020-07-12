from z3 import *
import time 

class Todo(Exception):
    pass

x, y, z = BitVecs('x y z', 32)

# We given an example for the special case of Fermat's Last Theorem when n==2,
# that is, we ask Z3 to show that x*x+y*y=z*z does have solutions.
def fermat_2(x, y, z):
    cons = []
    cons.append(x&0xffffff00 == 0)
    cons.append(y&0xffffff00 == 0)
    cons.append(z&0xffffff00 == 0)
    cons.append(x!=0)
    cons.append(y!=0)
    cons.append(z!=0)
    cons.append(x*x+y*y == z*z)
    return cons


# write a function for arbitrary n:
def fermat(x, y, z, n):
    '''
    add your implementation here:
    '''
    cons = []
    cons.append(x&0xffffff00 == 0)  # I can't understand why the magic number is that.
    cons.append(y&0xffffff00 == 0)
    cons.append(z&0xffffff00 == 0)
    cons.append(x!=0)
    cons.append(y!=0)
    cons.append(z!=0)
    def mul(k,n):
        temp = 1
        for _ in range(n):
            temp *= k
        return temp
        
    cons.append(mul(x,n)+mul(y,n) == mul(z,n))
    return cons


a,b,c = Ints('a b c')
def fermat_int(a, b, c, n):
    '''  测试整数，用来回答ppt上的问题
    '''
    cons = []
    max_number = 511
    cons.append(a<max_number)  # I can't understand why the magic number is that.
    cons.append(b<max_number)
    cons.append(c<max_number)
    cons.append(a!=0)
    cons.append(b!=0)
    cons.append(c!=0)
    def mul(k,n):
        temp = 1
        for _ in range(n):
            temp *= k
        return temp
        
    cons.append(mul(a,n)+mul(b,n) == mul(c,n))
    return cons


if __name__ == '__main__':
    # some unit tests
    solver = Solver()
    solver.add(fermat_2(x, y, z))
    res = solver.check()
    if res == sat:
        print("found a counter example, Fermat's Last Theorem does NOT held: ", solver.model())
    else:
        print("We are more confident that Fermat's Last Theorem does held, although we don't have a rigorous proof yet")
    solver = Solver()
    solver.add(fermat(x, y, z, 3))
    res = solver.check()
    start_time = time.time()
    if res == sat:
        print("found a counter example, Fermat's Last Theorem does NOT held: ", solver.model())
    else:
        print("We are more confident that Fermat's Last Theorem does held, although we don't have a rigorous proof yet")
    end_time = time.time()
    print('bit vec prove fermat:', end_time - start_time)

    solver = Solver()
    solver.add(fermat_int(a, b, c, 3))
    res = solver.check()
    start_time = time.time()
    if res == sat:
        print("found a counter example, Fermat's Last Theorem does NOT held: ", solver.model())
    else:
        print("We are more confident that Fermat's Last Theorem does held, although we don't have a rigorous proof yet")
    end_time = time.time()
    print('ints prove fermat:', end_time - start_time)