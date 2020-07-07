from enum import Enum
from typing import List
import imp_ast
import tac


###############################################
# a counter
counter = 0


def counter_next():
    global counter
    counter = counter + 1
    return f"L_{counter}"


###############################################
# to compile one statement
def compile_stm(s):
    if isinstance(s, imp_ast.StmAssign):
        result.append(tac.StmAssign(s.var, s.exp))
        return
    if isinstance(s, imp_ast.StmIf):
        tb = counter_next()
        fb = counter_next()
        rb = counter_next()
        new_stm = tac.StmIf(s.exp, tb, fb, -1, -1)
        result.append(new_stm)
        result.append(tac.StmLabel(tb))
        compile_stms(s.then_stms)
        result.append(tac.StmGoto(rb, -1))
        result.append(tac.StmLabel(fb))
        compile_stms(s.else_stms)
        result.append(tac.StmGoto(rb, -1))
        result.append(tac.StmLabel(rb))
        return
    if isinstance(s, imp_ast.StmWhile):
        entry = counter_next()
        tb = counter_next()
        rb = counter_next()
        result.append(tac.StmLabel(entry))
        result.append(tac.StmInv(s.inv, s.modified_vars))
        result.append(tac.StmIf(s.exp, tb, rb, -1, -1))
        result.append(tac.StmLabel(tb))
        compile_stms(s.stms)
        result.append(tac.StmGoto(entry, -1))
        result.append(tac.StmLabel(rb))
        return


result = []
# to compile a list of statements:
def compile_stms(stms: List[imp_ast.Stm]):
    for s in stms:
        compile_stm(s)


###############################################
# to compile a function:
def compile_fun(f: imp_ast.Function) -> tac.Function:
    global result
    result = []
    compile_stms(f.stms)
    result.append(tac.StmReturn(f.ret))
    return tac.Function(f.name,
                        f.args,
                        result,
                        f.pre,
                        f.post)


if __name__ == '__main__':
    f = compile_fun(imp_ast.fun_foo)
    print(f)
    f = tac.assemble(f)
    print(f)



