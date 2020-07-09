地址：http://staff.ustc.edu.cn/~bjhua/courses/theory/2020/assignment/assign5/index.html

partA 中的证明两个程序相等。

partB 部分作业的目的是定义两套语法 calc 和 tac, 在 compiler 中可以将 calc 编译为 tac.

重点：
- SSA: Static single assignment form, 即静态单赋值，这是一种中间表示形式，被称为单赋值的原因是每个名字在 SSA 中仅被赋值一次，同时尽在每个变量使用之前定义。