import z3
import imp_ast


class Todo(Exception):
    pass


def vc_2_z3(vc: imp_ast.Exp):
    if isinstance(vc, imp_ast.ExpNum):
        return vc.num

    if isinstance(vc, imp_ast.ExpVar):
        return z3.Int(vc.var)

    # TODO: your Exercise 5 code here, convert the generated
    # vc to z3 constraints format,
    # also do not forget to deal with ExpUni, Z3 is often
    # able to handle formulas involving quantifiers. like:
    # ForAll([x, y], f(x, y) == 0)
    if isinstance(vc, imp_ast.ExpBop):
        left = vc_2_z3(vc.left)
        right = vc_2_z3(vc.right)

        if vc.bop == imp_ast.BOp.ADD:
            return left + right
        elif vc.bop == imp_ast.BOp.MIN:
            return left - right
        elif vc.bop == imp_ast.BOp.MUL:
            return left * right
        elif vc.bop == imp_ast.BOp.DIV:
            return left / right
        elif vc.bop == imp_ast.BOp.EQ:
            return  left == right
        elif vc.bop == imp_ast.BOp.NE:
            return left != right
        elif vc.bop == imp_ast.BOp.GT:
            return left > right
        elif vc.bop == imp_ast.BOp.GE:
            return left >= right
        elif vc.bop == imp_ast.BOp.LT:
            return left < right
        elif vc.bop == imp_ast.BOp.LE:
            return left <= right
        elif vc.bop == imp_ast.BOp.IM:
            return z3.Implies( left, right)
        elif vc.bop == imp_ast.BOp.AND:
            return z3.And(left,right)
        elif vc.bop == imp_ast.BOp.OR:
            return z3.Or(left, right)
    if isinstance(vc, imp_ast.ExpNeg):
        return z3.Not( vc_2_z3( vc.exp))
    if isinstance(vc, imp_ast.ExpUni):
        exp = vc_2_z3(vc.exp)
        return z3.ForAll(z3.Ints(list(vc.vars_set)), exp)
    

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
