import counter
from z3 import *


class Todo(Exception):
    pass


##################################
# The abstract syntax for the Tac (three address code) language:

# statement
class Stm:
    pass


class StmAssignVar(Stm):
    def __init__(self, x, y):
        self.x = x
        self.y = y


class StmAssignAdd(Stm):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z


class StmAssignSub(Stm):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z


class StmAssignMul(Stm):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z


class StmAssignDiv(Stm):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z


# function:
class Function:
    def __init__(self, name, args, stms, ret):
        self.name = name
        self.args = args
        self.stms = stms
        self.ret = ret


# a pretty printer
def print_str(s, sep='', end=''):
    print(s, sep=sep, end=end)


def pp_stm(s):
    # TODO: your code here:
    raise Todo()


def pp_func(f):
    # TODO: your code here:
    raise Todo()


###############################################
# Generate Z3 constraints:
def gen_cons_stm(file, s):
    # TODO: your code here:
    raise Todo()


def gen_cons_func(file, f):
    # TODO: your code here:
    raise Todo()

###############################################
# SSA conversion:

# a map from variable to new variable:
var_map = {}


def to_ssa_stm(s):
    # TODO: your code here:
    raise Todo()


# take a function 'f', convert it to SSA
def to_ssa_func(f):
    # TODO: your code here:
    raise Todo()


if __name__ == '__main__':
    # a sample program:
    sample_f = Function('f',
                        ['x1', 'x2', 'y1', 'y2'],
                        [StmAssignAdd('t1', 'x1', 'y1'),
                         StmAssignAdd('t2', 'x2', 'y2'),
                         StmAssignMul('t3', 't1', 't2'),
                         StmAssignVar('z', 't3')],
                        'z')
    # print the original program
    pp_func(sample_f)
    # convert it to SSA
    ssa_for_f = to_ssa_func(sample_f)
    # print the converted program
    pp_func(ssa_for_f)
    # generate Z3 constraints
    gen_cons_func(ssa_for_f)
