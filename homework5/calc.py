import counter
from z3 import *


class Todo(Exception):
    pass


##################################
# The abstract syntax for the Calc language:
class Exp:
    pass


class ExpVar(Exp):
    def __init__(self, x):
        self.x = x


class ExpAdd(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ExpSub(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ExpMul(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ExpDiv(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right


# statement
class Stm:
    pass


class StmAssign(Stm):
    def __init__(self, x, e):
        self.x = x
        self.e = e


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


def pp_exp(e):
    if isinstance(e, ExpVar):
        print_str(e.x)
        return
    if isinstance(e, ExpAdd):
        print_str('(')
        pp_exp(e.left)
        print_str('+')
        pp_exp(e.right)
        print_str(')')
        return
    if isinstance(e, ExpSub):
        print_str('(')
        pp_exp(e.left)
        print_str('-')
        pp_exp(e.right)
        print_str(')')
        return
    if isinstance(e, ExpMul):
        print_str('(')
        pp_exp(e.left)
        print_str('*')
        pp_exp(e.right)
        print_str(')')
        return
    if isinstance(e, ExpDiv):
        print_str('(')
        pp_exp(e.left)
        print_str('/')
        pp_exp(e.right)
        print_str(')')
        return


def pp_stm(s):
    if isinstance(s, StmAssign):
        print_str(s.x)
        print_str('=')
        pp_exp(s.e)
        print_str(';\n')
        return


def pp_func(f):
    if isinstance(f, Function):
        print_str(f.name)
        print_str('(')
        for x in f.args:
            print_str(x)
            print_str(', ')
        print_str('){\n')
        for s in f.stms:
            pp_stm(s)
        print_str('return ')
        print_str(f.ret)
        print(';\n}\n')


###############################################
# Generate Z3 constraints:
def gen_cons_exp(file, e):
    if isinstance(e, ExpVar):
        file.write(e.x)
        return
    if isinstance(e, ExpAdd):
        file.write('f_add(')
        gen_cons_exp(file, e.left)
        file.write(', ')
        gen_cons_exp(file, e.right)
        file.write(')')
        return
    if isinstance(e, ExpSub):
        file.write('f_sub(')
        gen_cons_exp(file, e.left)
        file.write(', ')
        gen_cons_exp(file, e.right)
        file.write(')')
        return
    if isinstance(e, ExpMul):
        file.write('f_mul(')
        gen_cons_exp(file, e.left)
        file.write(', ')
        gen_cons_exp(file, e.right)
        file.write(')')
        return
    if isinstance(e, ExpDiv):
        file.write('f_div(')
        gen_cons_exp(file, e.left)
        file.write(', ')
        gen_cons_exp(file, e.right)
        file.write(')')
        return


def gen_cons_stm(file, s):
    if isinstance(s, StmAssign):
        file.write(s.x)
        file.write(' == ')
        gen_cons_exp(file, s.e)
        file.write(', ')
        return


def gen_cons_func(file, f):
    if isinstance(f, Function):
        print_str(f.name)
        # collect all variables
        vars = set()
        for a in f.args:
            vars.add(a)
        for s in f.stms:
            if isinstance(s, StmAssign):
                vars.add(s.x)
        # the declarations
        file.write('S = DeclareSort(\'S\')\n')
        for x in vars:
            file.write(x)
            file.write(', ')
        file.write('junk = Consts(\'')
        for x in vars:
            file.write(x)
            file.write(' ')
        file.write('junk\', S)\n')
        file.write('f_add = Function(\'f_add\', S, S, S)\n')
        file.write('f_sub = Function(\'f_sub\', S, S, S)\n')
        file.write('f_mul = Function(\'f_mul\', S, S, S)\n')
        file.write('f_div = Function(\'f_div\', S, S, S)\n\n')
        file.write('F = And(')
        for s in f.stms:
            gen_cons_stm(file, s)
        file.write(' True)\n\n')


def gen_cons_exp(e):
    if isinstance(e, ExpVar):
        return Const(e.x, DeclareSort('S'))
    if isinstance(e, ExpAdd):
        left = gen_cons_exp(e.left)
        right = gen_cons_exp(e.right)
        return z3.Function('f_add',
                        DeclareSort('S'),
                        DeclareSort('S'),
                        DeclareSort('S')).__call__(left, right)
    if isinstance(e, ExpSub):
        left = gen_cons_exp(e.left)
        right = gen_cons_exp(e.right)
        return z3.Function('f_sub',
                        DeclareSort('S'),
                        DeclareSort('S'),
                        DeclareSort('S')).__call__(left, right)
    if isinstance(e, ExpMul):
        left = gen_cons_exp(e.left)
        right = gen_cons_exp(e.right)
        return z3.Function('f_mul',
                        DeclareSort('S'),
                        DeclareSort('S'),
                        DeclareSort('S')).__call__(left, right)
    if isinstance(e, ExpDiv):
        left = gen_cons_exp(e.left)
        right = gen_cons_exp(e.right)
        return z3.Function('f_div',
                        DeclareSort('S'),
                        DeclareSort('S'),
                        DeclareSort('S')).__call__(left, right)


def gen_cons_stm(s):
    if isinstance(s, StmAssign):
        new_exp = gen_cons_exp(s.e)
        return Const(s.x, DeclareSort('S')) == new_exp


def gen_cons_func(f):
    cons = []
    if isinstance(f, Function):
        for s in f.stms:
            new_cons = gen_cons_stm(s)
            cons.append(new_cons)
        return cons


###############################################
# SSA conversion:

# a map from variable to new variable:
var_map = {}


def to_ssa_exp(e):
    if isinstance(e, ExpVar):
        return ExpVar(var_map[e.x])
    if isinstance(e, ExpAdd):
        new_left = to_ssa_exp(e.left)
        new_right = to_ssa_exp(e.right)
        return ExpAdd(new_left, new_right)
    if isinstance(e, ExpSub):
        new_left = to_ssa_exp(e.left)
        new_right = to_ssa_exp(e.right)
        return ExpSub(new_left, new_right)
    if isinstance(e, ExpMul):
        new_left = to_ssa_exp(e.left)
        new_right = to_ssa_exp(e.right)
        return ExpMul(new_left, new_right)
    if isinstance(e, ExpDiv):
        new_left = to_ssa_exp(e.left)
        new_right = to_ssa_exp(e.right)
        return ExpDiv(new_left, new_right)


def to_ssa_stm(s):
    if isinstance(s, StmAssign):
        new_e = to_ssa_exp(s.e)
        new_var = counter.fresh_var()
        var_map[s.x] = new_var
        return StmAssign(new_var, new_e)


# take a function 'f', convert it to SSA
def to_ssa_func(f):
    if isinstance(f, Function):
        # first, put every argument into the map
        for arg in f.args:
            var_map[arg] = arg
        # to convert each statement one by one:
        new_stms = []
        for s in f.stms:
            new_s = to_ssa_stm(s)
            new_stms.append(new_s)
        new_ret = var_map[f.ret]
        return Function(f.name, f.args, new_stms, new_ret)


if __name__ == '__main__':
    # a sample program:
    sample_f = Function('f',
                        ['x1', 'x2', 'y1', 'y2'],
                        [StmAssign('z', ExpMul(ExpAdd(ExpVar('x1'), ExpVar('y1')),
                                               ExpAdd(ExpVar('x2'), ExpVar('y2'))))],
                        'z')
    # print the original program
    pp_func(sample_f)
    # convert it to SSA
    new_f = to_ssa_func(sample_f)
    # print the converted program
    pp_func(new_f)
    # generate Z3 constraints
    gen_cons_func(new_f)
