import unittest

import pandas as pd
from pandas.testing import assert_series_equal

from constraint import Constraint, IllegalConstraintError
from tableau import Tableau


def simplex(constraints):
    result = {}
    if not constraints:
        return result

    print("===>Solving Constraints:")
    basic_var_amount = len(constraints[0].coefficients)
    for constraint in constraints:
        if len(constraint.coefficients) != basic_var_amount:
            raise IllegalConstraintError(constraint)
        print(constraint)

    tab = Tableau(constraints)

    # TODO: finish the simplex algorithm
    # if there is no solution, return string "no solution"
    # if find a solution, return the result as dict: e.g {"x0": 1, "x1": 1}
    # feel free to change the code here or add new class but your code should pass the unittest

    # Your code here

    print(f"===>Solving result is: {result}")
    return result


class TestSimplex(unittest.TestCase):

    def test_simplex_sat(self):
        case = [Constraint([1, 1], 2), Constraint([2, -1], 0), Constraint([-1, 2], 1)]
        result = simplex(case)
        assert_series_equal(pd.Series(result), pd.Series({"x0": 1.0, "x1": 1.0}))

    def test_simplex_unsat(self):
        case = [Constraint([-1, 1, 0], 0), Constraint([-1, 0, 1], 0), Constraint([1, -1, -2], 0),
                Constraint([0, 0, 1], 1)]
        result = simplex(case)
        self.assertEqual(result, "no solution")


if __name__ == '__main__':
    unittest.main()
