from z3 import *

import counter
import calc
import tac


class Todo(Exception):
    pass


###############################################
# a compiler from Calc to Tac.

# a map from variable to new variable:
all_stms = []


def emit_stm(s):
    global all_stms
    all_stms.append(s)


# invariant: compile an expression, return a variable
def compile_exp(e):
    if isinstance(e, calc.ExpVar):
        return e.x
    if isinstance(e, calc.ExpAdd):
        var_left = compile_exp(e.left)
        var_right = compile_exp(e.right)
        new_var = counter.fresh_var()
        emit_stm(tac.StmAssignAdd(new_var, var_left, var_right))
        return new_var
    # TODO: your code here:
    raise Todo()


def compile_stm(s):
    if isinstance(s, calc.StmAssign):
        new_var = compile_exp(s.e)
        emit_stm(tac.StmAssignVar(s.x, new_var))
        return


# take a function 'f', convert it to SSA
def compile_func0(f):
    global all_stms
    all_stms = []
    if isinstance(f, calc.Function):
        # to compile each statement one by one:
        for s in f.stms:
            compile_stm(s)
        return tac.Function(f.name, f.args, all_stms, f.ret)


def translation_validation(orig_f, result_f, orig_cons, result_cons):
    # TODO: for the compiler to be correct, you should prove this condition:
    # TODO:     orig_cons /\ result_cons -> x1==x2
    # TODO: your code here:
    raise Todo()


def compile_func(f):
    # print the original program:
    # calc.pp_func(f)
    # convert it to SSA:
    f_ssa = calc.to_ssa_func(f)
    # generate constraints:
    cons_before = calc.gen_cons_func(f_ssa)
    # print('the constraint is:')
    # print(cons_before)
    # compile the program:
    result_f = compile_func0(f_ssa)
    # print the converted program
    # tac.pp_func(result_f)
    # convert the result program to SSA:
    result_f_ssa = tac.to_ssa_func(result_f)
    # generate constraints on the target program:
    cons_after = tac.gen_cons_func(result_f_ssa)
    # translation validation the compiler:
    translation_validation(f_ssa, result_f_ssa, cons_before, cons_after)
    return result_f_ssa


if __name__ == '__main__':
    # a sample program:
    sample_f = calc.Function('f',
                             ['x1', 'x2', 'y1', 'y2'],
                             [calc.StmAssign('z', calc.ExpMul(calc.ExpAdd(calc.ExpVar('x1'), calc.ExpVar('y1')),
                                                              calc.ExpAdd(calc.ExpVar('x2'), calc.ExpVar('y2'))))],
                             'z')
    compile_func(sample_f)
