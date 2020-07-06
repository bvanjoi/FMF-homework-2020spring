from z3 import *


# We've been talking a lot of the satisfying problem, but using
# tools like Z3, we can also solve optimization problem.
# the 0-1 knapsack problem is often solved by the dynamic
# programming algorithm. But it's more natural and easier
# to solve with the LA theory.
# TODO: Exercise 6. 0-1 Knapsack problem.
# There are n items, with specific weight
# W = {w1, ..., wn}
# and value:
# V = {v1, ..., vn}
# For a given knapsack of capacity C, to choose some items
# such that:
#  wi+...+wk <= C
# and max(vi+...+vk).
#
# Now consider below condition:
# W = {4, 6, 2, 2, 5, 1}
# V = {8, 10, 6, 3, 7, 2}，
# C = 12
# Solve it with Z3.

W = [4, 6, 2, 2, 5, 1]
V = [8, 10, 6, 3, 7, 2]
C = 12
# create an optimizer
solver = Optimize()
vars = [Int('var_%d' % i) for i in range(len(W))]
weights = []
values = []

# Initialize weights and values
for i in range(len(W)):
    """your code here"""

# Add constraint wi+...+wk <= C
"""your code here"""

# Solve it via maximize
solver.maximize(sum(values))
print(solver.check())
maxValue = 0
m = solver.model()
for i in range(len(W)):
    if m[vars[i]] == 1:
        print(W[i], ': ', V[i])
        maxValue += V[i]

print('max value: ', maxValue)

