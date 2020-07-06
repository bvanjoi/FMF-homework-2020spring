from z3 import *

# TODO: Exercise 8
# Here the basic requirement is to solve Four Queens Problem
# But we also encourage you to try to implement a common method that can solve
# N queens which N can be arbitrary value.(Here we do not consider N to be a huge
# value).

# Init our board with N = 4
N = 4
board = [[Int('i_{}_{}'.format(i, j))for i in range(N)]
         for j in range(N)]

# TODO: Complete the remains.
def queens_quiz(...):
    raise Exception('TODO')


if __name__ == "__main__":
    queens_quiz()
