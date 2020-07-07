from z3 import *
from imp_ast import *
import prover


# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass


def var_substitution(var: str, exp: Exp, post_cond: Exp):
    if isinstance(post_cond, ExpNum):
        return post_cond
    # TODO: your Exercise 4 code here, do the variable substitution
    # do not forget deal with ExpUni here
    elif isinstance(post_cond, ExpVar):
        return post_cond.var
    elif isinstance(post_cond, ExpBop):
        return post_cond
    elif isinstance(post_cond, ExpNeg):
        return post_cond
    elif isinstance(post_cond, ExpUni):
        return post_cond


def vc_stms(stms: List[Stm],  post_cond: Exp):
    for stm in reversed(stms):
        post_cond = vc_stm(stm, post_cond)

    return post_cond


def vc_stm(stm: Stm, post_cond: Exp):
    if isinstance(stm, StmAssign):
        return var_substitution(stm.var, stm.exp, post_cond)

    # TODO: your Exercise 4 code here, generates verification conditions from statement
    # recall the rules:
    #
    # VC(x=e, P)          = P[x↦e]
    # VC(if(e;s1;s2), P)  = (e → VC(s1, P))∧(~e → VC(s2, P))
    # VC(while I(e;s), P) = I ∧ (∀(x1 x2 ... xn).I → (e → VC(s, I) ∧ (~e → P)))
    elif isinstance(stm, StmIf):
        return And( var_substitution(), var_substitution())
    elif isinstance(stm, StmWhile):
        for s in stm.stms:
            vc_stm(s, post_cond)

########################################
# This function will scan through a given function "f", generate and
# return a verification condition:
# VC(pre f(){S} post) = pre → VC(S, post)
def vc(func: Function) -> Exp:
    post_cond = var_substitution("result", func.ret, func.post)
    '''post_cond
    result == 5
    '''
    return ExpBop(func.pre, vc_stms(func.stms, post_cond), BOp.IM)


if __name__ == '__main__':
    # TODO: Exercise 4: perform verification condition generation, get the verification condition
    #
    # should print:
    #
    # (n <= 0) -> ((n <= 5) && ∀(n).((n <= 5) -> (((n < 5) -> ((n + 1) <= 5)) && (~(n < 5) -> (n == 5)))))
    # the number of nodes in VC:  15
    #
    # (n >= 0) -> (((0 <= (n + 1)) && ((2 * 0) == (0 * (0 - 1)))) && ∀(s,i).(((i <= (n + 1)) && ((2 * s) ==
    # (i * (i - 1)))) -> (((i <= n) -> (((i + 1) <= (n + 1)) && ((2 * (s + i)) == ((i + 1) * ((i + 1) - 1))))) &&
    # (~(i <= n) -> ((2 * s) == (n * (n + 1)))))))
    # the number of nodes in VC:  39
    #
    fill_in_modified_vars(fun_foo)
    '''fun_foo
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
    vc_foo = vc(fun_foo)
    print(vc_foo)
    '''vc_foo
    (n <= 0) -> None
    '''
    print("the number of nodes in VC: ", exp_num_nodes(vc_foo))

    fill_in_modified_vars(fun_sum)
    vc_sum = vc(fun_sum)
    print(vc_sum)
    print("the number of nodes in VC: ", exp_num_nodes(vc_sum))

    # TODO: Exercise 5: prove the generated vc with prove_vc(the_vc), you
    #  need to complete the code in prover.py file
    #
    # should output:
    #
    # Implies(n <= 0,
    #         And(n <= 5,
    #             ForAll(n,
    #                    Implies(n <= 5,
    #                            And(Implies(n < 5, n + 1 <= 5),
    #                                Implies(Not(n < 5), n == 5))))))
    #
    # Implies(n >= 0,
    #         And(And(n + 1 >= 0, True),
    #             ForAll([s, i],
    #                    Implies(And(i <= n + 1, 2*s == i*(i - 1)),
    #                            And(Implies(i <= n,
    #                                        And(i + 1 <= n + 1,
    #                                         2*(s + i) ==
    #                                         (i + 1)*(i + 1 - 1))),
    #                                Implies(Not(i <= n),
    #                                        2*s == n*(n + 1)))))))
    #
    # True
    # True
    #
    print(prover.prove_vc(vc_foo))
    print(prover.prove_vc(vc_sum))


