import sys
import time

def generate(n: int):
    f = open('large_prog.py', "w+")
    f.write("from imp_ast import *\n")
    f.write("import backward\n")
    f.write("\n")

    # the program
    f.write("fun_large_if = Function('large_if',\n\
                   ['x', 'y'],\n\
                   [\n")
    i = 0
    while i < n:
        f.write(" " * 12)
        f.write("StmIf(ExpBop(ExpVar('x'), ExpNum(")
        f.write(i.__str__())
        f.write("), BOp.LT), [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(")
        f.write(i.__str__())
        f.write("), BOp.ADD))], [StmAssign('y', ExpBop(ExpVar('x'), ExpNum(")
        f.write((i+1).__str__())
        f.write("), BOp.ADD))])")
        if i != n-1:
            f.write(', ')
        f.write('\n')
        i = i+1
    f.write(" " * 12)
    f.write("],\n")
    f.write(" " * 12)
    f.write("ExpVar('y'),\n")
    f.write(" " * 12)
    f.write("ExpBop(ExpVar('y'), ExpNum(0), BOp.GT),\n")
    f.write(" " * 12)
    f.write("ExpBop(ExpVar('y'), ExpNum(0), BOp.GT))\n")

    # diver
    f.write("\n\nif __name__ == '__main__':\n")
    f.write("    the_vc = backward.vc(fun_large_if)\n")
    f.write("    print(exp_num_nodes(the_vc))\n")
    f.write("\n")

    f.close()


if __name__ == '__main__':
    start_time = time.time()
    num_ifs = sys.argv[1]
    generate(int(num_ifs))
    end_time = time.time()
    print(end_time - start_time, 's')
