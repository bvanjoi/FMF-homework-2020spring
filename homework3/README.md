地址：http://staff.ustc.edu.cn/~bjhua/courses/theory/2020/assignment/assign3/index.html

SAT, z3

重点：
- 输出所有满足 SAT 的 boolean 值：当得到一个结果时，否认这个结果（哪个 命题 值为 true 则将它取 Not）, 再与原命题做 /\, 之后再检验可满足性。
- valid(P) <==> unsat(~P), valid 意为 永真
- dpll 算法：相较于枚举真值表(2^n)来检测可满足性，dpll 是一种更省时间的算法，
```cpp
// 伪代码描述
dpll( P){
    if(P == T) {
        return sat;
    } else if (P == F) {
        return unsat;
    }

    unitProp(P);  // unit prop and simplify P
    x = select_atomic(P)  // choose an atomic prop
    if ( dpll( P[x] -> T)){  // splitiing
        return sat;
    }
    return dpll( P[x] -> F);
}
```
- NNF: Negation normal form, 即否定范式，否定联结符的联结对象只是命题原子的公式
- CNF: Conjunctive normal form, 即合取范式，若干个析取子句的合取 