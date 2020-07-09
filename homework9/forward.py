from dataclasses import dataclass
from typing import Dict, Set, List

from backward import var_substitution
import imp_ast
import compiler
import tac
import prover


# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass


# for debugging
def print_rou(rou):
    rou_str = "\n".join([f"\t{var}: {value}" for var, value in rou.items()])
    print(f"rou: \n"
          f"{rou_str}\n")


# do the `rou(exp)` operation, transfer the expression by mapping variables to symbolic values
# similar to `symbolic_exp` function in assignment 8
def map_2_rou(exp: imp_ast.Exp, args: List[str], rou: Dict[str, imp_ast.Exp]) ->imp_ast.Exp:
    if isinstance(exp, imp_ast.ExpNum):
        return exp

    if isinstance(exp, imp_ast.ExpVar):
        rou_value = rou[exp.var]
        # avoid infinite recursion
        if exp.var in args:
            return rou_value
        else:
            return map_2_rou(rou_value, args, rou)

    if isinstance(exp, imp_ast.ExpBop):
        left = map_2_rou(exp.left, args, rou)
        right = map_2_rou(exp.right, args, rou)
        return imp_ast.ExpBop(left, right, exp.bop)

    if isinstance(exp, imp_ast.ExpNeg):
        return imp_ast.ExpNeg(map_2_rou(exp.exp, args, rou))


# get `rou_prime` by changing modified variables's mapping value in `rou` to a new ExpVar(var)
# `rou_prime=rou[(x1,..,xn) |-> (y1,..,yn)]` where `(y1,y2 ... ,yn)` are new variables,
# here we create `y` by adding `_prime` to original one's name.
def get_rou_prime(modified_vars: Set[str], rou: Dict[str, imp_ast.Exp]):
    rou_prime = rou.copy()
    renamed_modified_vars = set()

    for var in modified_vars:
        new_name = var+"_prime"
        rou_prime[var] = imp_ast.ExpVar(new_name)
        renamed_modified_vars.add(new_name)

    return rou_prime, renamed_modified_vars


########################################
# starting from the code position "pc", walk the code forward,
# maintaining the symbolic state (pc, rou, sigma), where:
# pc is the program counter, pointing to the next instruction to be executed;
# rou is the symbolic store, mapping variables to symbolic values;
# sigma is the invariant set
def vc(func: tac.Function, pc: int, rou: Dict[str, imp_ast.Exp], sigma: Set[int]) -> imp_ast.Exp:
    stm = func.stms[pc]

    if isinstance(stm, tac.StmLabel):
        pc += 1
        return vc(func, pc, rou, sigma)

    elif isinstance(stm, tac.StmGoto):
        return vc(func, stm.address, rou, sigma)

    # TODO: Exercise 9 code here:
    # recall the verification generation rules:
    #
    # VC(pc, rou, sigma) = VC(pc++, rou, sigma)                 pc->Label
    # VC(pc, rou, sigma) = VC(pc++, rou[x |-> rou(E)], sigma)   pc->x=E
    # VC(pc, rou, sigma) = VC(Label, rou, sigma)                pc->goto Label
    #
    # VC(pc, rou, sigma) = rou(E)->VC(L1,rou,sigma) /\
    #                      ~rou(E)->VC(L2,rou,sigma)            pc->if(E, L1, L2)
    #
    # VC(pc, rou, sigma) = rou(E) /\
    #                      (∀(y1...yn).rou_prime(E)->
    #                       VC(pc++, rou_prime, sigma.add(pc))   pc->inv E, pc not in sigma
    #                                                           where rou_prime = rou[(x1..xn)|->(y1..yn)]
    #                                                           (x1...xn) is modified variables
    #
    # VC(pc, rou, sigma) = rou(E)                               pc->inv E, pc in sigma
    #
    # VC(pc, rou, sigma) = rou(post["result" |-> E])            pc->return E
    elif isinstance(stm, tac.StmAssign):
        rou[stm.var] = map_2_rou(stm.exp, func.args, rou)
        pc += 1
        return vc(func, pc, rou, sigma)
    elif isinstance(stm, tac.StmIf):
        return imp_ast.ExpBop(
                imp_ast.ExpBop(                stm.exp,  vc(func, stm.true_address, rou, sigma), imp_ast.BOp.IM),
                imp_ast.ExpBop( imp_ast.ExpNeg(stm.exp), vc(func, stm.false_address, rou, sigma), imp_ast.BOp.IM),
                imp_ast.BOp.AND)
    elif isinstance(stm, tac.StmInv):
        if pc in sigma:
            return map_2_rou(stm.inv, func.args, rou)
        else:
            rou_prime, renamed_modified_vars = get_rou_prime(stm.modified_vars,rou)
            sigma.add(pc)
            pc += 1
            return imp_ast.ExpBop(
                    map_2_rou(stm.inv, func.args, rou),
                    imp_ast.ExpBop(
                        imp_ast.ExpUni(
                            renamed_modified_vars,
                            map_2_rou(stm.inv, func.args, rou_prime)),
                        vc( func, pc, rou_prime, sigma),
                    imp_ast.BOp.IM),
                   imp_ast.BOp.AND)
    elif isinstance(stm, tac.StmReturn):
        func.post = var_substitution("result", stm.e, func.post)
        return map_2_rou(func.post, func.args, rou)

def vc_func(func: tac.Function) -> imp_ast.Exp:
    rou_init = dict(zip(func.args, [imp_ast.ExpVar(arg) for arg in func.args]))

    pre_cond = map_2_rou(func.pre, func.args, rou_init)
    vc_cond = vc(func, 0, rou_init, set())

    # VC = 𝜌(pre) → vc(pc)
    return imp_ast.ExpBop(pre_cond, vc_cond, imp_ast.BOp.IM)


if __name__ == '__main__':
    # fill the modified variables in StmInv
    imp_ast.fill_in_modified_vars(imp_ast.fun_foo)
    '''imp_ast.fun_foo
    pre={n <= 0}
    foo(n){
        inv={n <= 5}
        modified_vars={n}
        while(n < 5){
                n = n + 1;
        }
        return n;
    }
    post={result == 5}
    '''
    # compile the source code to low-level code:
    f = compiler.compile_fun(imp_ast.fun_foo)
    print(f)
    ''' low-level code
    pre=n <= 0
    foo(n){
    L_1:
        inv=n <= 5, modified_vars={'n'}
        if(n < 5, L_2, L_3, -1, -1)
    L_2:
        n = n + 1
        goto L_1, -1
    L_3:
        return n
    }
    post=result == 5
    '''
    # convert the label address to physical address
    f = tac.assemble(f)
    print(f)
    '''f
    pre=n <= 0
    foo(n){
    L_1:
        inv=n <= 5, modified_vars={'n'}
        if(n < 5, L_2, L_3, 3, 6)
    L_2:
        n = n + 1
        goto L_1, 0
    L_3:
        return n
    }
    post=result == 5
    '''
    # generate verification conditions:
    the_vc = vc_func(f)

    #
    # TODO: Exercise 9: Finish this generator by filling missing code in the function vc()
    #  You'll be using the symbolic execution idea from previous assignment.
    #
    #  should print:
    #
    # (n <= 0) -> ((n <= 5) &&
    # ∀(n_prime).((n_prime <= 5) -> (((n_prime < 5) -> ((n_prime + 1) <= 5)) && (~(n_prime < 5) -> (n_prime == 5)))))
    # the number of nodes in VC:  15
    #
    print(the_vc)
    print("the number of nodes in VC: ", imp_ast.exp_num_nodes(the_vc))
    #
    # should print:
    #
    # Implies(n <= 0,
    #         And(n <= 5,
    #             ForAll(n_prime,
    #                    Implies(n_prime <= 5,
    #                            And(Implies(n_prime < 5,
    #                                        n_prime + 1 <= 5),
    #                                Implies(Not(n_prime < 5),
    #                                        n_prime == 5))))))
    #
    # convert and send the generated "the_vc" to Z3 solver,
    # to prove or disprove it:
    # should print:
    #
    #
    # True
    #
    print(prover.prove_vc(the_vc))

