#!/usr/bin/python3
# -*- coding: utf-8 -*-


from z3 import *


# Seat Arrangement
# Alice, Bob, Carol take 3 seats. But they have some requirements:
#   1. Alice can not sit near to Carol;
#   2. Bob can not sit right to Alice.
# Questions:
#   1. Is there any solution?
#   2. How many solutions in total?

# Now let us investigate the problem


def seat_arrangement():
    solver = Solver()
    # 1. First we need to modeling the problem
    # Let say:
    #   A_i means Alice takes seat Ai,
    #   B_i means Bob takes seat Bi,
    #   C_i means Carol takes seat Ci.
    # And since there are only 3 seats, so 1 <= i <= 3

    # Init.
    MAX_SEAT = 3
    # For Alice
    alice = [Int('a_%d' % i) for i in range(MAX_SEAT)]
    # 1 means alice takes this seat, 0 means not
    constraint_a = [Or(alice[i] == 0, alice[i] == 1) for i in range(MAX_SEAT)]
    solver.add(constraint_a)

    # TODO: Exercise 3
    """Fill your code here"""
    bob = [Int('b_%d' % i) for i in range(MAX_SEAT)]
    constraint_b = [Or(bob[i] == 0, bob[i] == 1) for i in range(MAX_SEAT)]
    solver.add(constraint_b)

    carol = [Int('c_%d' % i) for i in range(MAX_SEAT)]
    constraint_c = [Or(carol[i] == 0, carol[i] == 1) for i in range(MAX_SEAT)]
    solver.add(constraint_c)
    # Now let us consider the other constraints.
    # 0. First of all, keep in mind that one can only site one seat one time.
    #   Which means the Sum of each list should be 1
    #   Hints: Sum()
    constraint_0 = []
    constraint_0.append(Sum(alice) == 1)

    # TODO: Exercise 3
    """Fill your code here"""
    constraint_0.append(Sum(bob) == 1)
    constraint_0.append(Sum(carol) == 1)
    
    solver.add(constraint_0)

    # 1. Also, if one takes a seat, other can not take this seat.
    constraint_1 = []
    for i in range(MAX_SEAT):
        constraint_1.append(Sum(alice[i], bob[i], carol[i]) == 1)
    solver.add(constraint_1)

    # 2. Alice can not sit near to Carol
    #   It means that a[i] + c[i+1] = 1 and a[i] + c[i-1] = 1
    #   i, i+1, i-1 in range(MAX_SEAT)
    constraint_2 = []
    for i in range(MAX_SEAT):
        # TODO: Exercise 4
        """Fill your code here"""
        if i == 0:
            # == 1 意味着二者不能相邻； == 0 意味着 这个两个位置上必须有一个人，否则 unsat
            constraint_2.append( Or( Sum(alice[i], carol[i+1]) == 1, Sum(alice[i], carol[i+1]) == 0))
        elif i == 1:
            constraint_2.append( Or( Sum(alice[i], carol[i-1], carol[i+1]) == 1, Sum(alice[i], carol[i-1], carol[i+1]) == 0))
        elif i == 2:
            constraint_2.append( Or( Sum(alice[i], carol[i-1]) == 1, Sum(alice[i], carol[i-1]) == 0))
    solver.add(constraint_2)

    # 3. Bob can not sit right to Alice
    #   It means that a[i] + b[i+1] = 1
    #   i, i+1 in range(MAX_SEAT)
    constraint_3 = []
    for i in range(MAX_SEAT):
        if (i + 1) in range(MAX_SEAT):
            constraint_3.append(Or(Sum(alice[i], bob[i + 1]) == 1,
                                   Sum(alice[i], bob[i + 1]) == 0))
    solver.add(constraint_3)
    
    # print solution
    all_cell = alice + bob + carol
    while solver.check() == sat:
        m = solver.model()
        block = []
        for i in all_cell:
            if m[i] == 1:
                block.append(i == 1)
        solver.add(Not(And(block)))
    
    print(block)
    
if __name__ == "__main__":
    seat_arrangement()
