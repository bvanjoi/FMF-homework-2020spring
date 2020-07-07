from abc import abstractmethod, ABC

from z3 import *

# uninterrupted functions
S = Function("S", IntSort(), IntSort())
H = Function("H", IntSort(), IntSort())

class Todo(Exception):
    pass

# Term
class Term:
    @abstractmethod
    def to_z3(self):
        pass


class TVar(Term):
    def __init__(self, name, var):
        self.name = name
        self.var = var

    def __str__(self):
        # TODO: Implement the printing of `x`
        return f"{self.var}"

    def to_z3(self):
        # ⟦x⟧ = H(S(x))
        return H(S(self.var))


class TAdd(Term):
    def __init__(self, term, exp):
        self.term = term
        self.exp = exp

    def __str__(self):
        # TODO: Implement the printing of `T + E`
        return f'{self.term} + {self.exp}'

    def to_z3(self):
        # ⟦T + E⟧ = ⟦T⟧ + ⟦E⟧
        return self.term.to_z3() + self.exp.to_z3()


class TAddr(Term):
    def __init__(self, name, var):
        self.name = name
        self.var = var

    def __str__(self):
        # TODO: Implement the printing of `&x`
        return f'&{self.var}'


    def to_z3(self):
        return S(self.var)


class TAddrStar(Term):
    def __init__(self, term):
        self.term = term

    def __str__(self):
        # TODO: Implement the printing of `&*T`
        return f'&*{self.term}'


    def to_z3(self):
        # ⟦&*T⟧ = ⟦T⟧
        return self.term.to_z3()


class TStar(Term):
    def __init__(self, term):
        self.term = term

    def __str__(self):
        # TODO: Implement the printing of `*T`
        return f'*{self.term}'
                
    def to_z3(self):
        # ⟦*T⟧ = H(⟦T⟧)
        return H(self.term.to_z3())


class TNull(Term):
    def __str__(self):
        pass

    def to_z3(self):
        # ⟦NULL⟧ = 0
        return 0


# Expression
class Expression:
    @abstractmethod
    def to_z3(self):
        pass


class EVar(Expression):
    def __init__(self, name, var):
        self.name = name
        self.var = var

    def __str__(self):
        return self.name

    def to_z3(self):
        # TODO: Implement the translate procedure of `x`
        # [x] = H(S(x))
        return H(S(self.var))


class EConst(Expression):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return f"{self.value}"

    def to_z3(self):
        # TODO: Implement the translate procedure of `n`
        # [n] = n
        return self.value


class EAdd(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} + {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `E + E`
        # [E + E] = [E] + [E]
        return self.left.to_z3() + self.right.to_z3()

class EMinus(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} - {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `E - E`
        # [E - E] = [E] - [E]
        return self.left.to_z3() - self.right.to_z3()


class EStar(Expression):
    def __init__(self, term):
        self.term = term

    def __str__(self):
        return f"*{self.term}"

    def to_z3(self):
        # TODO: Implement the translate procedure of `*T`
        # [*T] = H(T)
        return H(self.term.to_z3())


# Relation
class Relation:
    @abstractmethod
    def to_z3(self):
        pass


class RTEq(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} = {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `T = T`
        # [T = T] = [T] = [T]
        return self.left.to_z3() == self.right.to_z3()


class RTLess(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} < {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `T < T`
        # [T < T] = [T] < [T]
        return self.left.to_z3() < self.right.to_z3()


class REEq(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} = {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `E = E`
        # [E = E] = [E] = [E]
        return self.left.to_z3() == self.right.to_z3()


class RELess(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} < {self.right})"

    def to_z3(self):
        # TODO: Implement the translate procedure of `E < E`
        # [E < E] = [E] < [E]
        return self.left.to_z3() < self.right.to_z3()


# Proposition:
class Proposition:
    @abstractmethod
    def to_z3(self):
        pass


class P(Proposition):
    def __init__(self, rel):
        self.rel = rel

    def __str__(self):
        return f"{self.rel}"

    def to_z3(self):
        # TODO: Implement the translate procedure of `P`
        return self.rel


class PNot(Proposition):
    def __init__(self, rel):
        self.rel = rel

    def __str__(self):
        return f"~{self.rel}"

    def to_z3(self):
        # TODO: Implement the translate procedure of `~ P`
        return Not(self.rel.to_z3())

class PAnd(Proposition):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        # TODO: Implement the printing of `P ∧ P`
        return f'({self.left} /\ {self.right})'

    def to_z3(self):
        # TODO: Implement the translate procedure of `P ∧ P`
        return And( self.left.to_z3(), self.right.to_z3())


def doit():
    p = Int("p")
    a = Int("a")

    # TODO Exercise 8: try to complete pointer logic printing method by implement the missing `__str__` methods in
    #  each class.
    p1 = PAnd(RTEq(TVar("p", p), TAddr("a", a)), REEq(EVar("a", a), EConst(1)))
    p2 = RTEq(TStar(TVar("p", p)), EConst(1))

    #  your code should print: ((p = &a) /\ (a = 1)) -> (*p = 1)
    print(f"{p1} -> {p2}")

    # TODO Exercise 9: finish the missing code in `to_z3()` methods, make it can translates pointer logic to z3's
    #  constraints. `to_z3()` methods in the `Term` class are already finished.
    prop = Implies(p1.to_z3(), p2.to_z3())

    # should print: Implies(And(H(S(p)) == S(a), H(S(a)) == 1), H(H(S(p))) == 1)
    print(prop)

    s = Solver()
    s.add(Not(prop))

    # should print: unsat
    print(s.check())


if __name__ == '__main__':
    doit()
