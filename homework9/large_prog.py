from imp_ast import *
import backward
import time
import prover
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
    print(fun_large_if)
    start_time = time.time()
    the_vc = backward.vc(fun_large_if)
    # print(the_vc)
    print(prover.prove_vc(the_vc))
    end_time = time.time()
    print(end_time - start_time, 's')
    print(exp_num_nodes(the_vc))


''' some questions.
1. How long does your code take to generate the VC? How to speed up this process?
当 num_ifs = 10 时生成的代码可以在很短时间完成，约 0.02s.
简单尝试了一下，但是当 num_ifs = 20 时，短时间内就无法生成了了。
话实在想不到加速的方法。

2. How large is the generated VC? How to shrink it?
可以使用三元表达式替换 if-else.

3. Is Z3 able to prove this VC? How long does Z3 take to finish the task? How to speed up?
是有解的 [x = -9, y = 1]. 但不是 validity.
解决 z3 prove num_ifs=10 时的 large_prop 约为 2s.
这里 pre 和 post 相同，可以考虑输入满足 pre 且能绕开所有 if-else 的变量。例如 [x= 10, y=1].
'''