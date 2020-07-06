from z3 import *

# TODO: Challenge: Task Scheduling
# Task Scheduling can be treated as a optimizing problem, too.

# Modeling the problem: use "selected[i] = 1" means task i is selected. Otherwise "selected[i] = 0".
# Modeling the constraint: use "selected[i] + selected[j] <= 1" to represent that task j overlaps with task i.
# Goal: max()


"""Your code here"""