from imp_ast import *
import backward

fun_large_if = Function('large_if',
                   ['x', 'y'],
                   [
            StmIf(ExpBop(ExpVar('x'), ExpNum(0), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(0), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(1), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(1), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(1), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(2), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(2), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(2), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(3), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(3), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(3), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(4), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(4), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(4), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(5), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(5), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(5), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(6), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(6), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(6), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(7), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(7), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(7), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(8), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(8), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(8), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(9), BOp.ADD))]), 
            StmIf(ExpBop(ExpVar('x'), ExpNum(9), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(9), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(10), BOp.ADD))])
            ],
            ExpVar('y'),
            ExpBop(ExpVar('y'), ExpNum(0), BOp.GT),
            ExpBop(ExpVar('y'), ExpNum(0), BOp.GT))


if __name__ == '__main__':
    the_vc = backward.vc(fun_large_if)
    print(exp_num_nodes(the_vc))

