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
    if isinstance( s, StmAssignVar):
        print_str(s.x)
        print_str('=')
        print_str(s.y)
        print_str(';\n')
    elif isinstance( s, StmAssignAdd):
        print_str(s.x)
        print_str('=')
        print_str(s.y)
        print_str('+')
        print_str(s.z)
        print_str(';\n')
    elif isinstance( s, StmAssignSub):
        print_str(s.x)
        print_str('=')
        print_str(s.y)
        print_str('-')
        print_str(s.z)
        print_str(';\n')
    elif isinstance( s, StmAssignMul):
        print_str(s.x)
        print_str('=')
        print_str(s.y)
        print_str('*')
        print_str(s.z)
        print_str(';\n')
    elif isinstance( s, StmAssignDiv):
        print_str(s.x)
        print_str('=')
        print_str(s.y)
        print_str('/')
        print_str(s.z)
        print_str(';\n')
  
    

def pp_func(f):
    # TODO: your code here:
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
def gen_cons_stm(file, s):
    # TODO: your code here:
    if isinstance( s, StmAssignVar):
        file.write(s.x)
        file.write('=')
        file.write(s.y)
    elif isinstance( s, StmAssignAdd):
        file.write(s.x)
        file.write('=')
        file.write('f_add(')
        file.write(s.y)
        file.write(',')
        file.write(s.z)
        file.write(')')
        file.write(',')

    elif isinstance( s, StmAssignSub):
        file.write(s.x)
        file.write('=')
        file.write('f_sub(')
        file.write(s.y)
        file.write(',')
        file.write(s.z)
        file.write(')')
        file.write(',')
    elif isinstance( s, StmAssignMul):
        file.write(s.x)
        file.write('=')
        file.write('f_mul(')
        file.write(s.y)
        file.write(',')
        file.write(s.z)
        file.write(')')
        file.write(',')
    elif isinstance( s, StmAssignDiv):
        file.write(s.x)
        file.write('=')
        file.write('f_div(')
        file.write(s.y)
        file.write(',')
        file.write(s.z)
        file.write(')')
        file.write(',')


def gen_cons_func(file, f):
    # TODO: your code here:
    if isinstance(f, Function):
        print_str(f.name)
        # collect all variables
        vars = set()
        for a in f.args:
            vars.add(a)
        for s in f.stms:
            vars.add(s.x)
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
# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
def gen_cons_stm(s):
    # TODO: your code here:
    if isinstance( s, StmAssignVar):
        return Const( s.x, DeclareSort('S')) == Const( s.y, DeclareSort('S'))
    left  = Const(s.y, DeclareSort('S'))
    right = Const(s.z, DeclareSort('S'))
    if isinstance( s, StmAssignAdd):
        return Const( s.x, DeclareSort('S')) == z3.Function('f_add', 
                                                    DeclareSort('S'),
                                                    DeclareSort('S'),
                                                    DeclareSort('S')).__call__(left, right)
    elif isinstance( s, StmAssignSub):
        return Const( s.x, DeclareSort('S')) == z3.Function('f_sub', 
                                                    DeclareSort('S'),
                                                    DeclareSort('S'),
                                                    DeclareSort('S')).__call__(left, right)
    elif isinstance( s, StmAssignMul):
        return Const( s.x, DeclareSort('S')) == z3.Function('f_mul', 
                                                    DeclareSort('S'),
                                                    DeclareSort('S'),
                                                    DeclareSort('S')).__call__(left, right)
    elif isinstance( s, StmAssignDiv):
        return Const( s.x, DeclareSort('S')) == z3.Function('f_div', 
                                                    DeclareSort('S'),
                                                    DeclareSort('S'),
                                                    DeclareSort('S')).__call__(left, right)

def gen_cons_func(f):
    # TODO: your code here:
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


def to_ssa_stm(s):
    # TODO: your code here:
    if isinstance( s, StmAssignVar):
        new_y = var_map[s.y]
        new_x = counter.fresh_var()
        var_map[s.x] = new_x
        return StmAssignVar(new_x, new_y)
       
    elif isinstance( s, StmAssignAdd):
        new_y = var_map[s.y]
        new_z = var_map[s.z]
        new_x = counter.fresh_var()
        var_map[s.x] = new_x
        return StmAssignAdd(new_x, new_y, new_z)

    elif isinstance( s, StmAssignSub):
        new_y = var_map[s.y]
        new_z = var_map[s.z]
        new_x = counter.fresh_var()
        var_map[s.x] = new_x
        return StmAssignSub(new_x, new_y, new_z)
    elif isinstance( s, StmAssignMul):
        new_y = var_map[s.y]
        new_z = var_map[s.z]
        new_x = counter.fresh_var()
        var_map[s.x] = new_x
        return StmAssignMul(new_x, new_y, new_z)
    elif isinstance( s, StmAssignDiv):
        new_y = var_map[s.y]
        new_z = var_map[s.z]
        new_x = counter.fresh_var()
        var_map[s.x] = new_x
        return StmAssignDiv(new_x, new_y, new_z)


# take a function 'f', convert it to SSA
def to_ssa_func(f):
    # TODO: your code here:
    if isinstance(f, Function):
        for arg in f.args:
            var_map[arg] = arg
        new_stms = []
        for s in f.stms:
            new_s = to_ssa_stm(s)
            new_stms.append(new_s)
        new_ret = var_map[f.ret]
        return Function( f.name, f.args, new_stms, new_ret)


if __name__ == '__main__':
    # a sample program:
    sample_f = Function('f',
                        ['x1', 'x2', 'y1', 'y2'],
                        [StmAssignAdd('t1', 'x1', 'y1'),
                         StmAssignAdd('t2', 'x2', 'y2'),
                         StmAssignMul('t3', 't1', 't2'),
                         StmAssignVar('z', 't3')],
                        'z')
    '''
    f(x1,x2,y1,y2) {
        t1 = x1 + y1
        t2 = x2 + y2
        t3 = t1 + t2
        z = t3
        return z
    }
    '''
    # print the original program
    pp_func(sample_f)
    # convert it to SSA
    ssa_for_f = to_ssa_func(sample_f)
    # print the converted program
    pp_func(ssa_for_f)
    # generate Z3 constraints
    ''' 之前的可以存储到 1.txt 中的代码
    fp = open(os.getcwd() + '/homework5/1.txt', 'w+')
    gen_cons_func(fp,ssa_for_f)
    fp.close()
    '''
    print(gen_cons_func(ssa_for_f))
    