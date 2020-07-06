import unittest
from constraint import Relation, Constraint, IllegalConstraintError
from tableau import Tableau
import numpy as np

def fourier_motzkin(constraints):
    # Implement the Fourier Motzkin algorithm
    #
    # The key idea of Fourier Motzkin algorithm is to
    # repeatedly eliminate variables, until SAT or UNSAT is obtained.
    # The procedure can be summarized as:
    # 1) Select a variable xi, and change the constraints into normal form,
    #    with m positive and n negative occurrences of xi:
    #
    #    xi + P1(x) >= 0
    #        ...
    #    xi + Pm(x) >= 0
    #    -xi + Q1(x) >= 0
    #        ...
    #    -xi + Qn(x) >= 0
    #    R(x) >= 0
    #
    # 2) Eliminate xi. The previous m + n constraints will be replaced with
    #    m * n new constraints.
    #
    #    P1(x) + Q1(x) >= 0
    #        ...
    #    P1(x) + Qn(x) >= 0
    #    P2(x) + Q1(x) >= 0
    #        ...
    #    P2(x) + Qn(x) >= 0
    #        ...
    #    Pm(x) + Qn(x) >= 0
    #    R(x) >= 0
    #
    # 3) If there're multiple variables in a single constraint, repeat step 1) and 2).

    result = {}
    print("===>Solving Constraints:")
    if not constraints:
        return result

    basic_var_amount = len(constraints[0].coefficients)
    for constraint in constraints:
        if len(constraint.coefficients) != basic_var_amount:
            raise IllegalConstraintError(constraint)
        print(constraint)
        #print(f"constraint.coefficients = {constraint.coefficients[1]}---constraint.value = {constraint.value}-----constraint.relation = {constraint.relation}")

    # TODO: finish the fourier_motzkin algorithm
    # if there is no solution, return string "no solution"
    # if find a solution, return the result as dict: e.g {"x0": 1, "x1": 1}
    # feel free to change the code here or add new code but your code should pass the unittest

    # Your code here
    
    vals = []
    #定义行列数,col为列数，row为行数
    lenrow = len(constraints)
    lencol = len(constraints[0].coefficients) + 1    
    #将LE转换为GE,并且正规化
    for constraint in constraints:        
        if constraint.relation == Relation.LE:
            for idx , coefficient in enumerate(constraint.coefficients):
                constraint.coefficients[idx] = coefficient * -1
            constraint.value = constraint.value * -1
            constraint.relation = Relation.GE
        if abs(constraint.coefficients[0]) != 1 :
            temp = abs(constraint.coefficients[0])
            constraint.coefficients[0] /= temp
            constraint.coefficients[1] /= temp
            constraint.value /= temp
        vals.append(constraint.value)
        
    tab = Tableau(constraints)
    tab.data.insert(loc = len(tab.data.columns) , column = "val" , value = vals)
    #将data转化为numpy数组形式
    constraints_np = tab.data.values
    #print(constraints_np)
    
    first_op_col = 0
    flag = 0
    for j in range(lencol - 1):
        first_op_col = j
        for count in range(lenrow- 1):
            for i in range(lenrow):
                if constraints_np[count][j] * constraints_np[i][j] < 0:
                    first_op_col = j
                    count = lenrow
                    j = lencol - 1
                    flag = 1
                    break
            if flag == 1:
                break
        if flag == 1 :
            break
    
    #print(f'first_op_col ={first_op_col}')
            
    #对first_op_col这一列进行消去
    privious_args = []
    count_nega = 0
    count_post = 0
    row_nega = 0
    row_post = 0
    row_final = 0
    for i in range(lenrow):
        if constraints_np[i][first_op_col] > 0:
            count_post += 1
            row_post = i
        else:
            count_nega += 1
            row_nega = i
    if count_post > count_nega:
        row_final = row_nega
    else :
        row_final = row_post
    #print(f'row_final = {row_final}')
    
    #记录原始参数
    for i in range(lencol):
        privious_args.append(constraints_np[row_final][i])
        
    #print(privious_args)
    #合并
    #print(constraints_np)
    #print('\n\n')
    for i in range(lenrow):  
        if i == row_final:
            continue    
        for j in range(lencol):             
            constraints_np[i][j] += privious_args[j]
    #print(constraints_np)
    
    #说明只有两个x系数
    if lencol == 3:
        for i in range(lenrow) :
            if i == row_final:
                continue
            for j in range(lencol - 1):
                if j != first_op_col:
                    constraints_np[i][2] /= constraints_np[i][j]
                    constraints_np[i][j] /= constraints_np[i][j]   
    print('\n\n')
    #print(constraints_np)
    
    ret = [0,0]
    ret_used = [0,0]
    ret_index = 0
    for i in range(lenrow):
        if(i == row_final):
            continue
        for j in range(lencol - 1):
            if j != first_op_col:
                if ret_used[j] == 1:
                    #或者是其他不对的条件
                    if constraints_np[i][2] != ret[j]:                      
                        return "no solution"
                else:
                    ret_used[j] = 1
                    ret_index = j
                    ret[j] = constraints_np[i][2]
                    
    #print(privious_args)
    if first_op_col == 0:
        ret[first_op_col] = privious_args[2] - privious_args[1] * ret[ret_index]
    else :
        ret[first_op_col] = privious_args[2] - privious_args[0] * ret[ret_index]
        ret[first_op_col] /= privious_args[1]
    
    #print(ret)
    for i in range(len(ret)):
        result[f'x{i}'] = round(ret[i],1)
    
    print(f"===>Solving result is {result}")
    return result


class TestFourierMotzkin(unittest.TestCase):

    def test_fourier_motzkin_sat(self):
        case = [Constraint([1, 1], 0.8), Constraint([1, -1], 0.2)]
        '''
        x0 + x1 >= 0.8
        x0 - x1 >= 0.2
        '''
        result = fourier_motzkin(case)
        self.assertDictEqual(result, {"x0": 0.5, "x1": 0.3})

    def test_fourier_motzkin_unsat(self):
        case = [Constraint([1, 1], 0.8), Constraint([1, 5], 0.2), Constraint([1, 3], 0, relation=Relation.LE)]
        '''
        x0 + x1 >= 0.8
        x0 + 5 * x1 >= 0.2
        x0 + 3 * x1 <= 0
        '''
        result = fourier_motzkin(case)
        self.assertEqual(result, "no solution")


if __name__ == '__main__':
    unittest.main()