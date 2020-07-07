import random
from dataclasses import dataclass
from typing import List, Dict

from z3 import *
from ast import *

from symbolic import check_cond, neg_exp, symbolic_exp, f1
from concrete import interpret_exp


# a concolic execution engine.

# concolic memory model will store arguments, concrete values, symbolic values
# and path condition list
@dataclass
class Memory:
    args: List[str]
    concrete_memory: Dict[str, int]
    symbolic_memory: Dict[str, Exp]
    path_condition: List[Exp]

    def __str__(self):
        arg_str = ",".join(self.args)
        actual_str = ",".join([f"{var} = {value}" for var, value in self.concrete_memory.items()])
        exp_str = "\n".join([f"\t{var} = {value}" for var, value in self.symbolic_memory.items()])
        cond_str = ",".join([str(cond) for cond in self.path_condition])
        return (f"Arguments: {arg_str}\n"
                f"Path Condition: {cond_str}\n"
                f"Actual Table: {actual_str}\n"
                f"Symbol Table: \n"
                f"{exp_str}\n")


#####################
#  concolic execution
def concolic_stm(memory, stm):
    if isinstance(stm, StmAssign):
        # TODO: Exercise 8 Code Here
        # process StmAssign by updating both symbolic memory and concrete memory
        memory.concrete_memory[stm.var] = interpret_exp(memory, stm.exp)
        memory.symbolic_memory[stm.var] = interpret_exp(memory, stm.exp)

        
    elif isinstance(stm, StmIf):
        # TODO: Exercise 8 Code Here
        # process StmIf statement
        if interpret_exp(memory, stm.exp):
            memory.path_condition.append( symbolic_exp(memory, stm.exp))
            memory = concolic_stms( memory, stm.then_stms)
        else:
            memory.path_condition.append(neg_exp(symbolic_exp(memory, stm.exp)))
            memory = concolic_stms(memory, stm.else_stms)

    elif isinstance(stm, StmWhile):
        # TODO: Exercise 9 Code Here
        # Executing the loop expression by concrete execution
        # to decide whether to continue.For the statements contained by
        # while-statement, do the concolic execution.
        if interpret_exp(memory, stm.exp):
            memory.path_condition.append(
                ExpBop( 
                    memory.symbolic_memory[stm.exp.left.var], 
                    memory.symbolic_memory[stm.exp.right.var],
                    stm.exp.bop))
            concolic_stms(memory, stm.stms)
        else:
            memory.path_condition.append( neg_exp(stm.exp))

    return memory


def concolic_stms(memory, stms):
    for stm in stms:
        concolic_stm(memory, stm)

    return memory


def concolic_func(func, init_concrete):
    # init memory
    init_symbolic = dict(zip(func.args, [ExpVar(arg) for arg in func.args]))
    memory = Memory(func.args, init_concrete, init_symbolic, [])

    concolic_stms(memory, func.stms)
    return memory, interpret_exp(memory, func.ret)


def concolic_executor(func, init_params, try_times):
    init_concrete = dict(zip(func.args, init_params))
    print(f"First Try, Input Value: {init_concrete}")
    memory, _ = concolic_func(func, init_concrete.copy())
    print(memory)

    # random select and negate one condition from previous result
    # and use z3 to generate a input to do next concolic execution
    for try_time in range(2, try_times+1, 1):
        random_idx = random.randrange(0, len(memory.path_condition))
        memory.path_condition[random_idx] = neg_exp(memory.path_condition[random_idx])
        ret, solver = check_cond(memory)

        if ret == sat:
            # use z3 result update new input values
            model = solver.model()
            for dec in model.decls():
                if dec.name() in func.args:
                    init_concrete[dec.name()] = model[dec].as_long()

            print(f"Try times: {try_time}, Input Value: {init_concrete}")
            memory, _ = concolic_func(func, init_concrete.copy())
            print(memory)
        else:
            print(f"Try times: {try_time}, Path conditions got UNSAT/UNKNOWN from z3")
            print(f"Conditions try to Solve: {solver}\n")


#####################
# test code
func_loop = Function("loop", ["m", "n"],
                     [StmWhile(ExpBop(ExpVar("m"), ExpVar("n"), BOp.LT),
                               [StmIf(ExpBop(ExpVar("m"), ExpNum(0), BOp.GT),
                                      [StmAssign("m", ExpBop(ExpVar("m"), ExpNum(2), BOp.MUL))],
                                      [StmIf(ExpBop(ExpVar("m"), ExpNum(0), BOp.EQ),
                                             [StmAssign("m", ExpNum(1))],
                                             [StmAssign("m", ExpBop(ExpVar("m"), ExpNum(-1), BOp.MUL))])])
                                ])
                     ], ExpVar("m"))

# example for challenge
hard_stm_1 = ExpBop(ExpBop(ExpBop(ExpVar("y"), ExpVar("y"), BOp.MUL), ExpVar("x"), BOp.MUL),
                    ExpBop(ExpVar("y"), ExpNum(23123), BOp.MUL), BOp.ADD)

func_foo = Function("foo", ["x", "y"],
                    [StmAssign("m", hard_stm_1),
                     StmIf(ExpBop(ExpVar("m"), ExpVar("y"), BOp.LE),
                           [StmAssign("s", ExpNum(1))],
                           [StmAssign("s", ExpNum(2))])
                     ], ExpVar("s"))


if __name__ == '__main__':
    # TODO: Exercise 8: Complete code in the function `concolic_stm` to
    # deal with `StmAssign` and `StmIf` statement, you need to maintain
    # both symbolic memory and concrete memory. Here you can
    # directly use the related functions in the `symbolic.py` and
    # `concrete.py` file
    #
    print(f1)

    # how many paths in `f1`?  How many times it has executed to cover all paths?
    '''3  paths, and in result, we try 5 times'''
    concolic_executor(f1, [0, 0], 5)
    print('----------------------')

    # TODO: Exercise 9: Fill code in the function `concolic_stm` to
    # deal with `StmWhile` statement. what you need to do is execute the
    # loop expression by concrete execution to decide whether to continue,
    # and for the statements contained by while-statement, do the concolic
    # execution. Don't forget to add the loop judgment expression to the
    # path condition list.
    #
    print(func_loop)

    # how many paths it covers in `func_loop`? How many times it has executed?
    '''4 paths, min times is 4.'''
    concolic_executor(func_loop, [2, 31], 20)
 