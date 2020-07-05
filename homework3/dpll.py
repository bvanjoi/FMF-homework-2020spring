from z3 import *

# In this problem, you will implement the DPLL algorithm as discussed
# in the class.

# a utility class to represent the code you should fill in.
class Todo(Exception):
    pass

########################################
# This bunch of code declare the syntax for the propositional logic, we
# repeat here:
'''
P ::= p
    | T
    | F
    | P /\ P
    | P \/ P
    | P -> P
    | ~P
'''


class Prop:
    pass


class PropVar(Prop):
    def __init__(self, var):
        self.var = var


class PropTrue(Prop):
    def __init__(self):
        pass


class PropFalse(Prop):
    def __init__(self):
        pass


class PropAnd(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class PropOr(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class PropImplies(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class PropNot(Prop):
    def __init__(self, p):
        self.prop = p


#####################
# We define pretty printing function.
def left_paren():
    print('(', sep='', end='')


def right_paren():
    print(')', sep='', end='')


def pp(prop):
    if prop.__class__ == PropVar:
        print(prop.var, sep='', end='')
        return
    if prop.__class__ == PropTrue:
        print('True', sep='', end='')
        return
    if prop.__class__ == PropFalse:
        print('False', sep='', end='')
        return
    if prop.__class__ == PropAnd:
        left_paren()
        pp(prop.left)
        right_paren()
        print('/\\', sep='', end='')
        left_paren()
        pp(prop.right)
        right_paren()
        return
    if prop.__class__ == PropOr:
        left_paren()
        pp(prop.left)
        right_paren()
        print('\\/', sep='', end='')
        left_paren()
        pp(prop.right)
        right_paren()
        return
    if prop.__class__ == PropImplies:
        left_paren()
        pp(prop.left)
        right_paren()
        print('->', sep='', end='')
        left_paren()
        pp(prop.right)
        right_paren()
        return
    if prop.__class__ == PropNot:
        left_paren()
        print('~', sep='', end='')
        pp(prop.prop)
        right_paren()
        return


# we can convert the above defined syntax into Z3's representation, so
# that we can check it's validity easily:
def toz3(prop):
    if prop.__class__ == PropVar:
        return Bool(prop.var)
    if prop.__class__ == PropImplies:
        return Implies(toz3(prop.left), toz3(prop.right))
    # Todo: add your code to handle other cases:
    if prop.__class__ == PropTrue:
        return True
    if prop.__class__ == PropFalse:
        return False
    if prop.__class__ == PropAnd:
        return And( toz3(prop.left), toz3(prop.right))
    if prop.__class__ == PropOr:
        return Or( toz3(prop.left), toz3(prop.right))
    if prop.__class__ == PropNot:
        return Not( toz3(prop.prop))


#####################
# a sample test program:
prop = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))
pp(prop)
z3prop = toz3(prop)
print('')
print(z3prop)
solver = Solver()
solver.add(Not(z3prop))
print(solver.check())

#####################
# TODO: please implement the nnf(), cnf() and dpll() algorithm, as discussed
# in the class.
def nnf(prop):
    '''convert the prop into nnf
    '''
    if prop.__class__ == PropImplies:
        return PropOr(PropNot(nnf( prop.left)), nnf( prop.right))
    if prop.__class__ == PropNot:
        if prop.prop.__class__ == PropVar:
            return prop
        if prop.prop.__class__ == PropTrue:
            return PropFalse()
        if prop.prop.__class__ == PropFalse:
            return PropTrue()
        if prop.prop.__class__ == PropAnd:
            return PropOr(nnf(PropNot(prop.prop.left)), nnf(PropNot(prop.prop.right)))
        if prop.prop.__class__ == PropOr:
            return PropAnd(nnf(PropNot(prop.prop.left)), nnf(PropNot(prop.prop.right)))
        if prop.prop.__class__ == PropImplies:
            return PropOr(nnf(prop.prop.left), nnf(prop.prop.right))
        if prop.prop.__class__ == PropNot:
            return nnf(prop.prop.prop)
    return prop


def cnf(prop):
    '''convert the prop into cnf
    '''
    if prop.__class__ == PropAnd:
        return PropAnd( cnf( prop.left), cnf(prop.right))
    if prop.__class__ == PropOr:
        if prop.left.__class__ == PropAnd:
            return PropAnd(cnf(PropOr(prop.left.left, prop.right)), cnf(PropOr(prop.left.right, prop.right)))
        if prop.right.__class__ == PropAnd:
            return PropAnd(cnf(PropOr(prop.left, prop.right.left)), cnf(PropOr(prop.left, prop.right.right)))
        return PropOr(cnf(prop.left), cnf(prop.right))
    return prop

def replaceProp(prop, p, value):
    if prop.__class__ == PropVar:
        if prop.var == p.var:
            return value
        return prop
    if prop.__class__ == PropAnd or prop.__class__ == PropOr:
        prop.left = replaceProp(prop.left, p, value)
        prop.right = replaceProp(prop.right, p, value)
    if prop.__class__ == PropNot:
        prop.prop = replaceProp(prop.prop, p, value)
    return prop

def unitProp(prop):
    if prop.__class__ == PropAnd:
        prop.left=unitProp(prop.left)
        prop.right=unitProp(prop.right)
        if prop.left.__class__ == PropTrue and prop.right.__class__ == PropTrue:
            return PropTrue()
        else:
            return PropFalse()
    if prop.__class__ == PropOr:
        prop.left=unitProp(prop.left)
        prop.right=unitProp(prop.right)
        if prop.left.__class__ == PropFalse and prop.right.__class__ == PropFalse:
            return PropFalse()
        else:
            return PropTrue()
    if prop.__class__ == PropNot:
        prop = PropNot(unitProp(prop.prop))
        if prop.prop.__class__ == PropFalse:
            return PropTrue()
        elif prop.prop.__class__ == PropTrue:
            return PropFalse()
    return prop

def select_automic(prop):
    if prop.__class__ == PropVar:
        return prop
    if prop.__class__ == PropAnd or prop.__class__ == PropOr:
        if select_automic(prop.left).__class__ != PropTrue and select_automic(prop.left).__class__ != PropFalse:
            return select_automic(prop.left)
        if select_automic(prop.right).__class__ != PropTrue and select_automic(prop.right).__class__ != PropFalse:
            return select_automic(prop.right)
        return unitProp(prop)
    if prop.__class__ == PropNot:
        return select_automic(prop.prop)
    return prop

def dpll(prop):
    prop = unitProp(prop)

    if prop.__class__ == PropTrue:
        return True
    elif prop.__class__ == PropFalse:
        return False
    
    p = select_automic(prop)
    
    if dpll(replaceProp(prop, p, PropTrue())):
        return True
    return dpll(replaceProp(prop, p, PropFalse()))

#####################
# Don't forget to write test cases to test your solution.
# prop: p-> ( q -> p)
# z3 formal: Implies(p, Implies(q, p))
# 该命题的否定为 unsat -> 该命题为 sat
print(dpll(cnf(nnf(prop))))
