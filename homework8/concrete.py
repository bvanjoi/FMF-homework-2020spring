import unittest
from dataclasses import dataclass
from typing import List, Dict

from ast import *

# a concrete execution engine.

# concrete execution memory model will store arguments and concrete values
@dataclass
class Memory:
    args: List[str]
    concrete_memory: Dict[str, int]

    def __str__(self):
        arg_str = ",".join(self.args)
        concrete_str = "\n".join([f"\t{var}: {value}" for var, value in self.concrete_memory.items()])
        return (f"Arguments: {arg_str}\n"
                f"Concrete Values: \n"
                f"{concrete_str}\n")

#####################
#  concrete execution
def interpret_exp(memory, exp):
    if isinstance(exp, ExpNum):
        return exp.num

    if isinstance(exp, ExpVar):
        # TODO: Exercise 2 Code Here
        # process ExpVar by reading the memory of variable x
        return memory.concrete_memory[exp.var]

    if isinstance(exp, ExpBop):
        # TODO: Exercise 2 Code Here
        # process ExpBop by the rules in the lecture note
        left  = exp.left
        right = exp.right

        if isinstance(left, ExpBop):
            left = interpret_exp(memory, left)
        elif isinstance(left, ExpNum):
            left = left.num
        else:
            left = memory.concrete_memory[left.var]
        
        if isinstance(right, ExpBop):
            right = interpret_exp(memory, right)
        elif isinstance(right, ExpNum):
            right = right.num
        else:
            right = memory.concrete_memory[right.var]

        if exp.bop == BOp.ADD:
            return left + right
        elif exp.bop == BOp.MIN:
            return left - right
        elif exp.bop == BOp.MUL:
            return left * right
        elif exp.bop == BOp.DIV:
            return left / right
        elif exp.bop == BOp.EQ:
            return left == right
        elif exp.bop == BOp.NE:
            return left != right
        elif exp.bop == BOp.GT:
            return left > right
        elif exp.bop == BOp.GE:
            return left >= right
        elif exp.bop == BOp.LT:
            return left < right
        else:
            return left <= right


def interpret_stm(memory, stm):
    if isinstance(stm, StmAssign):
        # TODO: Exercise 3 Code Here
        # process StmAssign by updating the memory
        memory.concrete_memory[stm.var] = interpret_exp(memory, stm.exp)

    elif isinstance(stm, StmIf):
        # TODO: Exercise 3 Code Here
        # process StmIf by the big-step rules
        if interpret_exp(memory, stm.exp):
            for s in stm.then_stms:
                interpret_stm( memory, s)
        else:
            for s in stm.else_stms:
                interpret_stm( memory, s)

    elif isinstance(stm, StmWhile):
        # TODO: Exercise 3 Code Here
        # process StmWhile by the big-step rules
        while interpret_exp(memory, stm.exp):
            for s in stm.stms:
                interpret_stm( memory, s)

    return memory


def interpret_stms(memory, stms):
    for stm in stms:
        interpret_stm(memory, stm)
    return memory


def interpret_func(func, params):
    assert len(func.args) == len(params), "The number of parameters does not match"
    memory = Memory(func.args, dict(zip(func.args, params)))
    interpret_stms(memory, func.stms)
    return interpret_exp(memory, func.ret)


#######################################
# test code
func_sum = Function('sum', ['n'],
                    [StmAssign('s', ExpNum(0)),
                     StmAssign('i', ExpNum(0)),
                     StmWhile(ExpBop(ExpVar('i'), ExpVar('n'), BOp.LE),
                              [StmAssign('s', ExpBop(ExpVar('s'), ExpVar('i'), BOp.ADD)),
                               StmAssign('i', ExpBop(ExpVar('i'), ExpNum(1), BOp.ADD))
                               ])
                     ], ExpVar('s'))

func_max = Function("max", ["m", "n"],
                    [StmAssign("c", ExpVar("m")),
                     StmIf(ExpBop(ExpVar("n"), ExpVar("c"), BOp.GT),
                           [StmAssign("c", ExpVar("n"))],
                           [])
                     ], ExpVar("c"))

func_gcd = Function("gcd", ["m", "n"],
                    [StmWhile(ExpBop(ExpVar("m"), ExpVar("n"), BOp.NE),
                              [StmIf(ExpBop(ExpVar("m"), ExpVar("n"), BOp.GE),
                                     [StmAssign("m", ExpBop(ExpVar("m"), ExpVar("n"), BOp.MIN))],
                                     [StmAssign("n", ExpBop(ExpVar("n"), ExpVar("m"), BOp.MIN))])
                               ])
                     ], ExpVar("m"))


class TestConcrete(unittest.TestCase):
    def test_interpret_exp(self):
        exp1 = ExpBop(ExpBop(ExpNum(3), ExpNum(2), BOp.ADD),
                      ExpBop(ExpNum(3), ExpNum(2), BOp.MUL),
                      BOp.GE)

        exp2 = ExpBop(ExpBop(ExpNum(10), ExpNum(2), BOp.DIV),
                      ExpBop(ExpNum(8), ExpNum(2), BOp.MIN),
                      BOp.NE)

        print(exp1)
        self.assertEqual(interpret_exp({}, exp1), False)

        print(exp2)
        self.assertEqual(interpret_exp({}, exp2), True)

    def test_interpret_func_sum(self):
        # print(func_sum)
        # and finally run this.
        # check 0 + 1 + 2 +... +100 == 5050
        self.assertEqual(interpret_func(func_sum, [100]), 5050)

    def test_interpret_func_max(self):
        # print(func_max)
        # second run this
        # max(10,20) == 20
        self.assertEqual(interpret_func(func_max, [10, 20]), 20)

    def test_interpret_func_gcd(self):
        # print(func_gcd)
        # first run this....
        # gcd(60,48) == 12
        self.assertEqual(interpret_func(func_gcd, [60, 48]), 12)


if __name__ == '__main__':
    unittest.main()
    