from z3 import *
import numpy as np
# TODO: Exercise 8
# Here the basic requirement is to solve Four Queens Problem
# But we also encourage you to try to implement a common method that can solve
# N queens which N can be arbitrary value.(Here we do not consider N to be a huge
# value).

# Init our board with N = 4
N = 8
board = [[Int('i_{}_{}'.format(i, j))for i in range(N)]
         for j in range(N)]

# TODO: Complete the remains.
def queens_quiz(N, board):
    solver = Solver()
    # 只能是 0 或 1, 分别代表该位置 无皇后，有皇后
    solver.add( [Or(board[i][j] == 0, board[i][j] == 1) for i in range(N) for j in range(N)] )
    # 行
    solver.add( [Sum( board[i]) == 1 for i in range(N) ])
    # 列
    temp = [ list(i) for i in np.array(board).T]
    solver.add( [ Sum( temp[i]) == 1 for i in range(N)])
    # 正对角线
    solver.add( [ Sum(i) <= 1 for i in [[board[i][0]] + [ board[i+j][j] for j in range(1,N) if i + j < N] for i in range(N)]] + [Sum(i) <= 1 for i in [[board[0][i]] + [ board[j][i+j] for j in range(1,N) if i + j < N] for i in range(N)]])
    # 反对角线
    solver.add( [ Sum(i) <= 1 for i in [[board[0][i]] + [board[j][i-j] for j in range(1,N) if i - j >= 0] for i in range(N)]] + [Sum(i) <= 1 for i in [[board[i][N-1]] + [ board[i+j][N-1-j] for j in range( 1,N) if i + j < N and N - i - j >= 0] for i in range(N)]])

    while solver.check() == sat:
        m = solver.model()     
        block = []
        for i in board:
            for j in i:
                if m[j] == 1:
                    block.append(j == 1)
        print(block)
        solver.add(Not(And(block)))

if __name__ == "__main__":
    queens_quiz(N,board)
