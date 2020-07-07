地址：http://staff.ustc.edu.cn/~bjhua/courses/theory/2020/assignment/assign6/index.html

本次作业结构看起来有些复杂，这里给出一些说明：

##### part1: 学习部分
- exercise.py: 对应 Exercise1, Exercise2.
- pandas_exercise.py: 对应 exercise5. 主要是用来学习 pandans 方便实现 simplex.

##### part2: 理论算法实现部分
- constraint.py: 构建了 Constraint 类，详细说明可见该脚本下的注释
- fourier_motzkin.py: fourizer——motzkin Variable Elimination 算法的实现
- tableau.py: 对应 exercise6, 实现了 pivot 函数，该函数可以实现变量转化，可见 simplex 中的示例。
- simplex.py: simplex 算法的实现，由于这个是 challenge, 咱们就不写了哈[doge]

##### part3: 应用
用 LA 解决以下问题：
- seat_arrangement.py: 座位问题
- 01knapsack.py: 0-1背包，最优化问题
- four_queen.py: 四皇后

--------------

重点：
- Guassian elimination: 即高斯消去
```
对于方程组
x + y = 0.8
x - y = 0.2
另二式相加，得到 2x = 1, 
进而得到 x = 0.5 
再代入得到 y = 0.3
```
- Fourier-Motzkin Variable Elimination: 重复消去变量，直到获得 SAT 或 UNSAT. 该算法在实数范围内存在指数爆炸的问题，对于比较小的范围比较有实际价值。

1. 首先 normalize, 对于某个变量，最终形式为：
```
x_i + P_1(x) >= 0
    .... 
x_i + P_m(x) >= 0

-x_i + Q_1(x) >= 0
    ....
-x_i + Q_n(x) >= 0

R(x) >= 0
```
上式中，P(x), Q(x), R(x) 均不包含变量 x_i.

2. 消去 x_i
```
P_1(x) + Q_1(x) >= 0
...
P_1(x) + Q_n(x) >= 0

...

P_m(x) + Q_1(x) >= 0
...
P_m(x) + Q_n(x) >= 0

R(x) >= 0
```

示例：
```
方程组：
x - y <= 0
x - z <= 0
-x + y + 2z <= 0
-z <= -1

消去 x 后
2z <= 0
y + z <= 0
-z <= -1

再消去 z
0 <= -2
y <= -1

-> UNSAT
```

- Simplex:

示例：
```
对于不等式：
x + y >= 2
2x - y >= 0
-x + 2y >= 1

1. 首先，将不等式转化为以下形式：
x + y - s1 = 0
2x - y - s2 = 0
-x + 2y -s3 = 0
s1 >= 2
s2 >= 0
s3 >= 1

2. 初始时令 x = 0, y = 0, 得到
s1 = 0 不满足 
s2 = 0
s3 = 0 不满足

3. 首先修复 s1,
s1 =  x +  y ->  x =  s1 -  y
s2 = 2x -  y -> s2 = 2s1 - 3y
s3 = -x + 2y -> s3 = -s1 + 3y
令 s1 = 2, y = 0 得到
x  =  2
s2 =  4
s3 = -2 不满足

4. 修复 s3
s3 = -s1 + 3y -> y  = s1/3 + s3/3
x  =  s1 -  y -> x  = 2 * s1/3 - s3/3
s2 = 2s1 - 3y -> s2 = s1 - s3
令 s1 = 2, s3 = 1 得到
x = 1
y = 1
s2 = 1

satisfied!
```