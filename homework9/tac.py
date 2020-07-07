from enum import Enum
from typing import List, Set
from imp_ast import Exp, ExpBop, ExpVar, ExpNum, BOp


# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass


########################################
# This bunch of code declare the syntax for the intermediate language: TAC.
# we reuse the expressions from abstract syntax trees, for it's unchanged.

###############################################
# statement


class Stm:
    def __init__(self):
        pass

    def __repr__(self):
        return str(self)


class StmAssign(Stm):
    def __init__(self, var: str, exp: Exp):
        super().__init__()
        self.var = var
        self.exp = exp

    def __str__(self):
        return f"\t{self.var} = {self.exp}\n"


class StmIf(Stm):
    def __init__(self, exp: Exp, true_label: str, false_label: str, true_address: int, false_address: int):
        super().__init__()
        self.exp = exp
        self.true_label = true_label
        self.false_label = false_label
        self.true_address = true_address
        self.false_address = false_address

    def __str__(self):
        return f"\tif({self.exp}, {self.true_label}, {self.false_label}, {self.true_address}, {self.false_address})\n"


class StmLabel(Stm):
    def __init__(self, label: str):
        super().__init__()
        self.label = label

    def __str__(self):
        return f"{self.label}:\n"


class StmGoto(Stm):
    def __init__(self, label: str, address: int):
        super().__init__()
        self.label = label
        self.address = address

    def __str__(self):
        return f"\tgoto {self.label}, {self.address}\n"


class StmInv(Stm):
    def __init__(self, inv: Exp, modified_vars: Set[str]):
        super().__init__()
        self.inv = inv
        self.modified_vars = modified_vars

    def __str__(self):
        return f"\tinv={self.inv}, modified_vars={self.modified_vars}\n"


class StmReturn(Stm):
    def __init__(self, e: Exp):
        super().__init__()
        self.e = e

    def __str__(self):
        return f"\treturn {self.e}\n"


###############################################
# function
class Function:
    def __init__(self, name: str, args: List[str], stms: List[Stm], pre: Exp, post: Exp):
        self.name = name
        self.args = args
        self.stms = stms
        self.pre = pre
        self.post = post

    def __str__(self):
        arg_str = ",".join(self.args)

        stms_str = "".join([str(stm) for stm in self.stms])

        return (f"pre={self.pre}\n"
                f"{self.name}({arg_str}){{\n"
                f"{stms_str}"
                f"}}\n"
                f"post={self.post}\n\n")


# given a function, to calculate the physical address
# according to the label address.
# that is, we should jump to address, instead of labels.
# this is achieved by an assembler.
def assemble(f: Function) -> Function:
    # we first build a dict, mapping labels to their address
    label_dict = {}
    i = 0
    for s in f.stms:
        if isinstance(s, StmLabel):
            label_dict[s.label] = i
        i = i+1
    # debugging
    #print('label_dict=', label_dict)
    # rewrite the program to fix the address
    for s in f.stms:
        if isinstance(s, StmIf):
            s.true_address = label_dict[s.true_label]
            s.false_address = label_dict[s.false_label]
        if isinstance(s, StmGoto):
            s.address = label_dict[s.label]
    return f


