from enum import Enum


class Relation(Enum):
    GE = ">="
    LE = "<="


class IllegalConstraintError(Exception):
    def __init__(self, constraint):
        self.constraint = constraint

    def __str__(self):
        return f"Illegal constraint: {self.constraint}"


class Constraint:
    '''构建 Constraint 类
    coefficients 为一个 list, 下标为 i 的值为 x_i 的系数
    value 为右侧的值
    relation 为类型 >= or <=
    '''
    def __init__(self, coefficients, value, relation=Relation.GE):
        '''
        default:  >=
        '''
        self.coefficients = coefficients
        self.value = value
        self.relation = relation

    def __str__(self):
        coefficients_str = ""
        for idx, value in enumerate(self.coefficients):
            if idx == 0:
                coefficients_str += f"{value}*x{idx}"
            elif value > 0:
                coefficients_str += f" + {value}*x{idx}"
            elif value < 0:
                coefficients_str += f" - {abs(value)}*x{idx}"

        return f"{coefficients_str} {self.relation.value} {self.value}"


if __name__ == '__main__':
    A = [Constraint([1, 1], 2), Constraint([2, -1], 0), Constraint([-1, 2], 1, Relation.LE)]
    for constr in A:
        print(constr)
