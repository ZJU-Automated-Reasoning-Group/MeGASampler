import z3
from z3 import help_simplify, unsat, With, Int, Bool, Array, IntSort, Select, Store

from test_formula_to_intervals import read_smt2, solve_and_strengthen_formula, solve_formula
from z3_utils import *
import sys as _sys
from formula_strengthener import strengthen, remove_or, nnf_simplify


def built_in_tests():
    print(f"z3 version: {z3.Z3_get_full_version()}")

    x = Int("x")
    y = Int("y")
    z = Int("z")
    t = Int("t")

    b = Bool("b")

    I = IntSort()
    a = Array("a", I, I)
    b = Array("b", I, I)
    c = Array("c", I, I)

    # f = And((Select(a, x) == 3), (Select(a, 0) == 8))
    # test_formula(f)
    #
    # f = Select(a, Select(b, y)) > Select(Store(a, 0, 4), z)
    # test_formula(f)
    #
    # f = Select(a, Select(b, y)) > Select(Store(a, x, 4), z)
    # test_formula(f)
    #
    # f = Select(Store(Store(a, x, 0), y, 1), z) > 8
    # test_formula(f)
    #
    # f = Select(
    #            Store(Store(a, x, 0),
    #                  Select((Store(a, y, 1)), 5),
    #                  1),
    #            z) > 8
    # test_formula(f)
    #
    # f = Select(
    #            Store(Store(a, x, 0),
    #                  Select((Store(a, y, 1)), 5),
    #                  1),
    #            z) > Select(a, x + y)
    # test_formula(f)

    # f = Store(a, x, x) == Store(a, y, y)
    # test_formula(f)

    # f = And(Select(a, x) > 9, Select(a, y) <= 50, x == y)
    # test_formula(f)

    f = And(Select(a, x) > 9, Select(b, y) <= 50, x == y)
    test_formula(f)

    # f = And(Select(Store(a, 0, 10), x) > 9, Select(b, y) <= 50, x == y)
    # test_formula(f)


def test_formula(f):
    print("--------------")
    print(f"f is: {f}")
    f_simple = nnf_simplify(f, True)
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
    f_intervals = strengthen(f, m, isAUF=True)
    print(f"interval formula is: {f_intervals}")
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
