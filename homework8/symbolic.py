import multiprocessing as mp
from dataclasses import dataclass
from typing import List, Dict

from z3 import *
from ast import *

# a symbolic execution engine.

# symbolic execution memory model will store arguments, symbolic values and path condition
@dataclass
class Memory:
    args: List[str]
    symbolic_memory: Dict[str, Exp]
    path_condition: List[Exp]

    def __str__(self):
        arg_str = ",".join(self.args)
        exp_str = "\n".join([f"\t{var} = {value}" for var, value in self.symbolic_memory.items()])
        cond_str = ",".join([str(cond) for cond in self.path_condition])
        return (f"Arguments: {arg_str}\n"
                f"Path Condition: {cond_str}\n"
                f"Symbol Memory: \n"
                f"{exp_str}\n")


# negate the condition
def neg_exp(exp):
    if exp.bop is BOp.EQ:
        return ExpBop(exp.left, exp.right, BOp.NE)
    if exp.bop is BOp.NE:
        return ExpBop(exp.left, exp.right, BOp.EQ)
    if exp.bop is BOp.GT:
        return ExpBop(exp.left, exp.right, BOp.LE)
    if exp.bop is BOp.GE:
        return ExpBop(exp.left, exp.right, BOp.LT)
    if exp.bop is BOp.LT:
        return ExpBop(exp.left, exp.right, BOp.GE)
    if exp.bop is BOp.LE:
        return ExpBop(exp.left, exp.right, BOp.GT)

#####################
# compile AST expression to Z3
def exp_2_z3(exp):
    if isinstance(exp, ExpNum):
        return exp.num
    if isinstance(exp, ExpVar):
        # TODO: Exercise 7 Code Here
        # transfer the ExpVar to z3 Int
        return Int( str(exp.var))
    if isinstance(exp, ExpBop):
        # TODO: Exercise 7 Code Here
        # transfer the ExpBop
        if exp.bop == BOp.ADD:
            return (exp_2_z3(exp.left) + exp_2_z3(exp.right))
        elif exp.bop == BOp.MIN:
            return (exp_2_z3(exp.left) - exp_2_z3(exp.right))
        elif exp.bop == BOp.MUL:
            return (exp_2_z3(exp.left) * exp_2_z3(exp.right))
        elif exp.bop == BOp.DIV:
            return (exp_2_z3(exp.left) / exp_2_z3(exp.right))
        elif exp.bop == BOp.EQ:
            return (exp_2_z3(exp.left) == exp_2_z3(exp.right))
        elif exp.bop == BOp.NE:
            return (exp_2_z3(exp.left) != exp_2_z3(exp.right))
        elif exp.bop == BOp.GT:
            return (exp_2_z3(exp.left) > exp_2_z3(exp.right))
        elif exp.bop == BOp.GE:
            return (exp_2_z3(exp.left) >= exp_2_z3(exp.right))
        elif exp.bop == BOp.LT:
            return (exp_2_z3(exp.left) < exp_2_z3(exp.right))
        elif exp.bop == BOp.LE:
            return (exp_2_z3(exp.left) <= exp_2_z3(exp.right))
        


# use Z3 to solve conditions
def check_cond(memory, add_cond=None):
    solver = Solver()

    # add path condition
    for cond in memory.path_condition:
        solver.add(exp_2_z3(cond))
        
    # add additional condition
    if add_cond:
        for cond in add_cond:
            solver.add(exp_2_z3(symbolic_exp(memory, cond)))

    check_result = solver.check()

    return check_result, solver

#####################
#  symbolic execution
def symbolic_exp(memory, exp):
    if isinstance(exp, ExpNum):
        return exp

    if isinstance(exp, ExpVar):
        # TODO: Exercise 5 Code Here
        # transfer the ExpVar to Exp which only contains argument variables
        # and ExpNum
        var = memory.symbolic_memory[str(exp.var)]

        if isinstance(var, ExpVar):
            return ExpVar(var)
        elif isinstance(var, ExpNum):
            return symbolic_exp(memory, var)
        elif str(var.left) == str(exp) or str(var.right) == str(exp):
            ''' prevent stack overflow
            '''
            return ExpBop(var.left, var.right, var.bop)
        return ExpBop(symbolic_exp(memory, var.left), symbolic_exp(memory, var.right),var.bop)
        
    if isinstance(exp, ExpBop):
        # TODO: Exercise 5 Code Here
        # transfer ExpBop's left and right expression recursive
        return ExpBop(symbolic_exp(memory, exp.left), symbolic_exp(memory, exp.right),exp.bop)

def symbolic_stm(memory, stm, rest_stms, results):
    if isinstance(stm, StmAssign):
        # TODO: Exercise 6 Code Here
        # process StmAssign by updating symbolic memory
        memory.symbolic_memory[stm.var] = symbolic_exp(memory,stm.exp)
        symbolic_stms(memory, rest_stms, results)

        
    if isinstance(stm, StmIf):
        # TODO: Exercise 6 Code Here
        # process StmIf by forking two processes
        # one of them will symbolic execute then_stms and rest_stms
        # other one will symbolic execute else_stms and rest_stms
        # also, start them and wait them to join
        rest_stmsthen = [ i for i in stm.then_stms]
        rest_stmselse = [ i for i in stm.else_stms]
        
        for i in rest_stms:
            rest_stmsthen.append(i)
            rest_stmselse.append(i)

        p1 = mp.Process(target = symbolic_stms,args = (memory,rest_stmsthen,results, stm.exp))
        p2 = mp.Process(target = symbolic_stms,args = (memory,rest_stmselse,results, neg_exp(stm.exp)))
        p1.start()
        p2.start()
        p1.join()
        p2.join()
        

def symbolic_stms(memory, stms, results, condition=None):
    if condition:
        memory.path_condition.append(symbolic_exp(memory, condition))

    if not stms:
        results.put(memory)
    else:
        symbolic_stm(memory, stms[0], stms[1:], results)

    return results


def symbolic_function(func):
    # init memory
    init_params = [ExpVar(arg) for arg in func.args]
    memory = Memory(func.args, dict(zip(func.args, init_params)), [])

    results = symbolic_stms(memory, func.stms, mp.SimpleQueue())
    result_list = []

    while not results.empty():
        result = results.get()
        print(result)
        result_list.append(result)

    return result_list


###############################
# test code
f1 = Function('f2', ['a', "b"],
              [StmAssign('x', ExpNum(1)),
               StmAssign('y', ExpNum(0)),
               StmIf(ExpBop(ExpVar('a'), ExpNum(0), BOp.NE),
                     [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(3), BOp.ADD)),
                      StmIf(ExpBop(ExpVar('b'), ExpNum(0), BOp.EQ),
                            [StmAssign('x', ExpBop(ExpNum(2), ExpBop(ExpVar('a'), ExpVar('b'), BOp.ADD), BOp.MUL))],
                            [])],
                     [])
               ], ExpVar('x'))


if __name__ == '__main__':

    example_memory = Memory(args=["a", "b", "c"],
                            symbolic_memory={"a": ExpVar("a"),
                                             "b": ExpBop(ExpNum(42), ExpVar("a"), BOp.MIN),
                                             "c": ExpBop(ExpVar("c"), ExpNum(20), BOp.ADD),
                                             "m": ExpBop(ExpVar("b"), ExpNum(5), BOp.MUL),
                                             "n": ExpBop(ExpVar("c"), ExpNum(2), BOp.MUL)},
                            path_condition=[])
    print(example_memory)
    example_exp = ExpBop(ExpVar("m"), ExpVar("n"), BOp.EQ)
    # TODO: Exercise 5: Fill code in the function `symbolic_exp`
    # You should replace the variables in the expression according to the
    # symbolic memory. The result will be an expression only contains argument
    # variables(ExpVar("arg") and ExpNum.
    #
    # Exercise 5 Should output:
    #
    # [m == n]  ===>  [((42 - a) * 5) == ((c + 20) * 2)]
    #
    '''
    c = c + 20 may caused stack overflow.
    '''
    
    print(f"[{example_exp}]  ===>  [{symbolic_exp(example_memory, example_exp)}]\n")

    # TODO: Exercise 6: Fill code in the function `symbolic_stm`
    # Here you should deal with `StmAssign` and `StmIf`, the `StmAssign`
    # will update the symbolic memory; In the `StmIf` you should do the branch
    # splitting, recall how to use Python's multiprocessing in Exercise 4
    #
    # Should output(the order may different):
    #
    # Arguments: a,b
    # Path Condition: a == 0
    # Symbol Memory:
    #   a = a
    #   b = b
    #   x = 1
    #   y = 0
    #
    # Arguments: a,b
    # Path Condition: a != 0, b != 0
    # Symbol Memory:
    #   a = a
    #   b = b
    #   x = 1
    #   y = 1 + 3
    #
    # Arguments: a,b
    # Path Condition: a != 0, b == 0
    # Symbol Memory:
    #   a = a
    #   b = b
    #   x = 2 * (a + b)
    #   y = 1 + 3
    #
    print(f1)
    result_memories = symbolic_function(f1)
    # TODO: Exercise 7: Fill code in the function `exp_2_z3`.
    # make it can transfers the conditions(AST Node) to z3 constraints.
    # note that our program only contains integer number
    #
    # Should output:
    #
    # Conditions: [a != 0, b == 0, 2 * (a + b) - 4 == 0]
    # SAT Input: a = 2, b = 0
    #

    # additional condition need to check: x - y = 0
    check_conditions = [ExpBop(ExpBop(ExpVar('x'), ExpVar('y'), BOp.MIN), ExpNum(0), BOp.EQ)]
    
    for result_memory in result_memories:
        ret, s = check_cond(result_memory, check_conditions)
        if ret == sat:
            print(f"Conditions: {s}")
            print(f"SAT Input: {s.model()}")
