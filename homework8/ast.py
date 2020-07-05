from enum import Enum
from typing import List

# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass


########################################
# This bunch of code declare the syntax for the language C--, as we
# discussed in the class:
'''
bop ::= + | - | * | / | == | != | > | < | >= | <=
E   ::= n | x | E bop E
S   ::= skip
      | x=E
      | S;S
      | f(E1, …, En)
      | if(E, S, S)
      | while(E, S)
F   ::= f(x1, …, xn){S; return E;}
'''
##################################
# bops


class BOp(Enum):
    ADD = "+"
    MIN = "-"
    MUL = "*"
    DIV = "/"
    EQ = "=="
    NE = "!="
    GT = ">"
    GE = ">="
    LT = "<"
    LE = "<="

##########################################
# expressions


class Exp:
    pass


class ExpNum(Exp):
    def __init__(self, n: int):
        self.num = n

    def __str__(self):
        return f"{self.num}"


class ExpVar(Exp):
    def __init__(self, var: str):
        self.var = var

    def __str__(self):
        return f"{self.var}"


class ExpBop(Exp):
    def __init__(self, left: Exp, right: Exp, bop: BOp):
        self.left = left
        self.right = right
        self.bop = bop

    def __str__(self):
        if isinstance(self.left, ExpBop):
            left_str = f"({self.left})"
        else:
            left_str = f"{self.left}"

        if isinstance(self.right, ExpBop):
            right_str = f"({self.right})"
        else:
            right_str = f"{self.right}"

        return f"{left_str} {self.bop.value} {right_str}"


###############################################
# statement

class Stm:
    def __init__(self):
        self.level = 0

    def __repr__(self):
        return str(self)


class StmAssign(Stm):
    def __init__(self, var: str, exp: Exp):
        super().__init__()
        self.var = var
        self.exp = exp

    def __str__(self):
        
        indent_space = self.level * "\t"
        return f"{indent_space}{self.var} = {self.exp};\n"


class StmIf(Stm):
    def __init__(self, exp: Exp, then_stms: List[Stm], else_stms: List[Stm]):
        super().__init__()
        self.exp = exp
        self.then_stms = then_stms
        self.else_stms = else_stms

    def __str__(self):
        # TODO: Exercise 1 Code Here
        for stm in self.then_stms:
            stm.level = self.level + 1
        for stm in self.else_stms:
            stm.level = self.level + 1

        indent_space = self.level * "\t"

        then_stms_str = "".join([ str(stm) for stm in self.then_stms])
        else_stms_str = "".join([ str(stm) for stm in self.else_stms])

        res = (f"{indent_space}if({self.exp}){{\n"
                f"{then_stms_str}"
                f"{indent_space}}}\n")
        if len(else_stms_str):
            res += (f"{indent_space}else{{\n"
                    f"{else_stms_str}"
                    f"{indent_space}}}\n")

        return res
            

class StmWhile(Stm):
    def __init__(self, exp: Exp, stms: List[Stm]):
        super().__init__()
        self.exp = exp
        self.stms = stms

    def __str__(self):
        # TODO: Exercise 1 Code Here
        for stm in self.stms:
            stm.level = self.level + 1
        indent_space = self.level * "\t"
        stms_str = "".join([ str(stm) for stm in self.stms])
        
        return (f"{indent_space}while({self.exp}){{\n"
                f"{stms_str}"
                f"{indent_space}}}\n")

###############################################
# function
class Function:
    def __init__(self, name: str, args: List[str], stms: List[Stm], ret: Exp):
        self.name = name
        self.args = args
        self.stms = stms
        self.ret = ret

    def __str__(self):
        arg_str = ",".join(self.args)
        for stm in self.stms:
            stm.level += 1

        stms_str = "".join([str(stm) for stm in self.stms])

        return (f"{self.name}({arg_str}){{\n"
                f"{stms_str}"
                f"\treturn {self.ret};\n"
                f"}}\n")
