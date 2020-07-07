import z3
import imp_ast


class Todo(Exception):
    pass


def vc_2_z3(vc: imp_ast.Exp):
    if isinstance(vc, imp_ast.ExpNum):
        return vc.num

    if isinstance(vc, imp_ast.ExpVar):
        return z3.Int(vc.var)

    raise Todo()
    # TODO: your Exercise 5 code here, convert the generated
    # vc to z3 constraints format,
    # also do not forget to deal with ExpUni, Z3 is often
    # able to handle formulas involving quantifiers. like:
    # ForAll([x, y], f(x, y) == 0)


def prove_vc(vc: imp_ast) -> bool:
    solver = z3.Solver()
    vc_z3 = vc_2_z3(vc)
    # debugging:
    print(vc_z3)
    solver.add(z3.Not(vc_z3))
    res = solver.check()
    if res == z3.unsat:
        return True
    else:
        print(solver.model())
        return False

