from z3 import *

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
        for i in range(n):
            temp *= k
        return temp
        
    cons.append(mul(x,n)+mul(y,n) == mul(z,n))
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
    solver.add(fermat(x, y, z, 4))
    res = solver.check()
    if res == sat:
        print("found a counter example, Fermat's Last Theorem does NOT held: ", solver.model())
    else:
        print("We are more confident that Fermat's Last Theorem does held, although we don't have a rigorous proof yet")

