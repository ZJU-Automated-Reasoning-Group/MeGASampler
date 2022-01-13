from z3 import help_simplify, unsat, With, Int, Bool, Array, IntSort, Select, Store

from python.test_formula_to_intervals import read_smt2, solve_and_strengthen_formula, solve_formula
from z3_utils import *
import sys as _sys
from formula_strengthener import strengthen, remove_or, nnf_simplify


def built_in_tests():
    x = Int("x")
    y = Int("y")
    z = Int("z")
    t = Int("t")

    b = Bool("b")

    I = IntSort()
    a = Array("a", I, I)
    b = Array("b", I, I)
    c = Array("c", I, I)

    f = And((Select(a, x) == 3), (Select(a, 0) == 8))
    test_formula(f)

    f = Select(a, Select(b, y)) > Select(Store(a, 0, 4), z)
    test_formula(f)


def test_formula(f):
    print("--------------")
    print(f"f is: {f}")
    f_simple = nnf_simplify(f)
    print(f"f_simple is: {f_simple}")
    # sanity check that f=f_simple
    res, m = solve_formula(Or(And(f, Not(f_simple)), (And(Not(f), f_simple))))
    assert res == unsat
    # now solve f_simple
    res, m = solve_formula(f_simple)
    if res != sat:
        print("formula is not satisfiable")
        return
    print(f"m is: {m}")
    f_slice = remove_or(f_simple, m)
    print(f"slice is: {f_slice}")
    # strengthen(f_slice, m)
    print("--------------")


if __name__ == "__main__":
    sys_args = _sys.argv[1:]
    if len(sys_args) == 0:
        print("No files were given. Running built-in tests.")
        built_in_tests()
    for file in sys_args:
        print(f"reading from file: {file}")
        # help_simplify()
        constraints = read_smt2(file) # file-error handling is done inside read_smt2
        f = And(constraints)
        test_formula(f)
        # m = solve_formula(f)
        # f_L = slice_formula(f, m)
        # print(f_L)
