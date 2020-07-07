from enum import Enum
from typing import List, Set

# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass

########################################
# This bunch of code declare the syntax for the language C--, as we
# discussed in the class.
# but we add bop implication: ->, add: &&, or: ||
# and negation: ~, universal quantification: ∀
'''
bop ::= + | - | * | / | == | != | > | < | >= | <= | ->
E   ::= n | x | E bop E | ~E | ∀(x1, …, xn).E
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
    IM = "->"
    AND = "&&"
    OR = "||"


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


class ExpNeg(Exp):
    def __init__(self, exp: Exp):
        self.exp = exp

    def __str__(self):
        return f"~({self.exp})"


class ExpUni(Exp):
    def __init__(self, vars_set: Set[str], exp: Exp):
        self.vars_set = vars_set
        self.exp = exp

    def __str__(self):
        vars_str = ",".join(self.vars_set)
        return f"∀({vars_str}).({self.exp})"


# given an expression "e", to calculate the number of nodes
# in this expression. this number is useful to estimate
# how large this expression is, and how much memory it will occupy.
def exp_num_nodes(exp: Exp) -> int:
    if isinstance(exp, ExpNum):
        return 1
    if isinstance(exp, ExpVar):
        return 1
    if isinstance(exp, ExpBop):
        return exp_num_nodes(exp.left) + exp_num_nodes(exp.right)
    if isinstance(exp, ExpNeg):
        return exp_num_nodes(exp.exp)
    if isinstance(exp, ExpUni):
        pass

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
        indent_space = self.level * "\t"

        for stm in self.then_stms:
            stm.level = self.level + 1

        for stm in self.else_stms:
            stm.level = self.level + 1

        then_stms_str = "".join([str(stm) for stm in self.then_stms])
        else_stms_str = "".join([str(stm) for stm in self.else_stms])

        then_str = (f"{indent_space}if({self.exp}){{\n"
                    f"{then_stms_str}"
                    f"{indent_space}}}\n")

        if self.else_stms:
            return (f"{then_str}"
                    f"{indent_space}else{{\n"
                    f"{else_stms_str}"
                    f"{indent_space}}}\n")
        else:
            return then_str


class StmWhile(Stm):
    def __init__(self, inv: Exp, modified_vars: Set[str], exp: Exp, stms: List[Stm]):
        super().__init__()
        self.inv = inv
        self.modified_vars = modified_vars
        self.exp = exp
        self.stms = stms

    def __str__(self):
        indent_space = self.level * "\t"
        for stm in self.stms:
            stm.level = self.level + 1

        stms_str = "".join([str(stm) for stm in self.stms])
        modified_vars = ",".join(self.modified_vars)

        return (f"{indent_space}inv={{{self.inv}}}\n"
                f"{indent_space}modified_vars={{{modified_vars}}}\n"
                f"{indent_space}while({self.exp}){{\n"
                f"{stms_str}"
                f"{indent_space}}}\n")


###############################################
# function
class Function:
    def __init__(self, name: str, args: List[str], stms: List[Stm], ret: Exp, pre: Exp, post: Exp):
        self.name = name
        self.args = args
        self.stms = stms
        self.ret = ret
        self.pre = pre
        self.post = post

    def __str__(self):
        arg_str = ",".join(self.args)
        for stm in self.stms:
            stm.level += 1

        stms_str = "".join([str(stm) for stm in self.stms])

        return (f"pre={{{self.pre}}}\n"
                f"{self.name}({arg_str}){{\n"
                f"{stms_str}"
                f"\treturn {self.ret};\n"
                f"}}\n"
                f"post={{{self.post}}}\n")


# for a given function "f", this function crawl through this function,
# for each while statement in the function, record the modified
# vars on the while statement. Notice the nesting of loops.
def fill_in_modified_vars(f: Function):
    '''标记处 循环内 改动的变量
    TODO
    注意，每个 stmwhile 中都有带有一个 modified_vars
    '''
    def is_modified_vars(stm):
        if isinstance(stm, StmAssign) and stm.var != stm.exp:
            return stm.var

    def loop_stms(stms):
        if isinstance(stms, StmAssign):
            return set(stms.var)
        elif isinstance(stms, StmWhile):
            for stm in stms.stms:
                if is_modified_vars(stm):
                    stms.modified_vars.add(stm.var)
                elif isinstance(stm, StmWhile):
                    stms.modified_vars |= loop_stms(stm)
                elif isinstance(stm, StmIf):
                    for s in stm.then_stms:
                        stms.modified_vars |= loop_stms(s)
                    for s in stm.else_stms:
                        stms.modified_vars |= loop_stms(s)
        elif isinstance(stms, StmIf):
            for stm in stms.then_stms:
                loop_stms(stm)
            for stm in stms.else_stms:
                loop_stms(stm)
             
            return set()
        return stms.modified_vars

    for stm in f.stms:
        loop_stms(stm)

#####################
# test case
'''
pre={n <= 0}
foo(n){
    inv={n <= 5}
    modified_vars={}
    while(n < 5){
        n = n + 1;
    }
    return n;
}
post={result == 5}
'''
fun_foo = Function('foo',
                   ['n'],
                   [StmWhile(ExpBop(ExpVar('n'), ExpNum(5), BOp.LE),
                             set(),
                             ExpBop(ExpVar('n'), ExpNum(5), BOp.LT),
                             [StmAssign('n', ExpBop(ExpVar('n'), ExpNum(1), BOp.ADD))])],
                   ExpVar('n'),
                   ExpBop(ExpVar('n'), ExpNum(0), BOp.LE),
                   ExpBop(ExpVar('result'), ExpNum(5), BOp.EQ))


##########
# test case for exercise 3
fun_loop = Function("loop",
                    ["m", "n"],
                    [StmAssign('a', ExpNum(0)),
                     StmAssign("b", ExpNum(0)),
                     StmWhile(ExpBop(ExpVar('n'), ExpNum(0), BOp.GE),
                              set(),
                              ExpBop(ExpVar('m'), ExpNum(0), BOp.LE),
                              [StmAssign('m', ExpBop(ExpVar('n'), ExpNum(1), BOp.MIN)),
                               StmWhile(ExpBop(ExpVar('n'), ExpNum(0), BOp.GE),
                                        set(),
                                        ExpBop(ExpVar('n'), ExpNum(0), BOp.LE),
                                        [StmAssign('a', ExpBop(ExpVar('a'), ExpNum(1), BOp.ADD)),
                                         StmAssign('b', ExpBop(ExpVar('b'), ExpNum(2), BOp.ADD))
                                         ])
                               ]),
                     StmAssign("d", ExpNum(5)),
                     StmIf(ExpBop(ExpVar('n'), ExpVar('m'), BOp.GE),
                           [StmAssign("b", ExpBop(ExpVar('b'), ExpVar('a'), BOp.ADD))],
                           [StmWhile(ExpBop(ExpVar('d'), ExpNum(0), BOp.GE),
                                     set(),
                                     ExpBop(ExpVar('d'), ExpNum(0), BOp.GT),
                                     [StmIf(ExpBop(ExpVar('d'), ExpVar('n'), BOp.GE),
                                            [StmAssign('a', ExpBop(ExpVar('a'), ExpVar('d'), BOp.ADD)),
                                             StmAssign('d', ExpBop(ExpVar('d'), ExpNum(1), BOp.MIN))
                                             ],
                                            [StmAssign('b', ExpBop(ExpVar('b'), ExpVar('d'), BOp.MIN)),
                                             StmAssign('d', ExpBop(ExpVar('d'), ExpNum(2), BOp.MIN))
                                             ]),
                                      ])
                            ])
                     ],
                    ExpVar('a'),
                    ExpBop(ExpVar('n'), ExpNum(0), BOp.LE),
                    ExpBop(ExpVar('m'), ExpNum(0), BOp.GE),)


#####################
# fill in the function "sum" below:
# def __init__(self, name: str, args: List[str], stms: List[Stm], ret: Exp, pre: Exp, post: Exp):

fun_sum = Function("sum",
                   ['n'],
                   [StmAssign('s', ExpNum(0)),
                    StmAssign('i', ExpNum(0)),
                    StmWhile(ExpBop(ExpBop( ExpVar('i'), ExpBop(ExpVar('n'),ExpNum(1),BOp.ADD), BOp.LE),
                                    ExpBop(
                                        ExpBop(ExpNum(2), ExpVar('s'), BOp.MUL), 
                                        ExpBop(ExpVar('i'), ExpBop(ExpVar('i'),ExpNum(1),BOp.MIN) ,BOp.MUL), 
                                        BOp.EQ),
                                    BOp.AND),
                              set(),
                              ExpBop(ExpVar('i'), ExpVar('n'), BOp.LE),
                              [
                                StmAssign('s', ExpBop(ExpVar('s'),ExpVar('i') ,BOp.ADD)),
                                StmAssign('i', ExpBop(ExpVar('i'),ExpNum(1) ,BOp.ADD))
                              ]), 
                   ],
                   ExpVar('s'),
                   ExpBop(ExpVar('n'), ExpNum(0), BOp.GE),
                   ExpBop( ExpBop(ExpVar('result'), ExpNum(2), BOp.MUL) ,ExpBop(ExpVar('n'), ExpBop( ExpVar('n'), ExpNum(1), BOp.ADD), BOp.MUL), BOp.EQ))


if __name__ == '__main__':
    print(fun_foo)

    # TODO: Exercise 1: write down your definition for the above function "sum"
    #
    # should print:
    #
    # pre={n >= 0}
    # sum(n){
    #     s = 0;
    #     i = 0;
    #     inv={(i <= (n + 1)) && ((2 * s) == (i * (i - 1)))}
    #     modified_vars={}
    #     while(i <= n){
    #         s = s + i;
    #         i = i + 1;
    #     }
    #     return s;
    # }
    # post={(2 * result) == (n * (n + 1))}
    #
    print(fun_sum)
    # TODO: Exercise 2:  Complete function exp_num_nodes(), to count the number of nodes in a given expression.
    #
    # should print：
    #
    # post condition of sum(n) has 5 nodes
    # invariant in the while statement of sum(n) has 8 nodes
    #
    print(f"post condition of sum(n) has {exp_num_nodes(fun_sum.post)} nodes")
    print(f"invariant in the while statement of sum(n) has {exp_num_nodes(fun_sum.stms[2].inv)} nodes\n")

    # TODO: Exercise 3: Calculate the modified_var in any while statement by filling in the
    #  function fill_in_modified_vars() module. Or you can modify the data structures to add new member
    #  methods if you prefer OO-style.
    #
    # should print：
    #
    # first while statement's modified_vars is: {'a', 'm', 'b'}
    # second while statement's modified_vars is: {'a', 'b'}.
    # third while statement's modified_vars is: {'a', 'b', 'd'}
    #
    ''' fun_loop
    pre={n <= 0}
    loop(m,n){
            a = 0;
            b = 0;
            inv={n >= 0}
            modified_vars={}
            while(m <= 0){
                    m = n - 1;
                    inv={n >= 0}
                    modified_vars={}
                    while(n <= 0){
                            a = a + 1;
                            b = b + 2;
                    }
            }
            d = 5;
            if(n >= m){
                    b = b + a;
            }
            else{
                    inv={d >= 0}
                    modified_vars={}
                    while(d > 0){
                            if(d >= n){
                                    a = a + d;
                                    d = d - 1;
                            }
                            else{
                                    b = b - d;
                                    d = d - 2;
                            }
                    }
            }
            return a;
    }
    post={m >= 0}
    '''
    fill_in_modified_vars(fun_loop)

    print(f"first while statement's modified_vars is: {fun_loop.stms[2].modified_vars}")
    print(f"second while statement's modified_vars is: {fun_loop.stms[2].stms[1].modified_vars}.")
    print(f"third while statement's modified_vars is: {fun_loop.stms[4].else_stms[0].modified_vars}")