from z3_utils import *
import sys as _sys
from formula_strengthener import strengthen
import timeit


def wrapper(func, *args, **kwargs):
    def wrapped():
        return func(*args, **kwargs)
    return wrapped


def strengthen_formula_test(f, debug = False):
    s = Solver()
    s.add(f)
    s.check()
    m = s.model()
    r = strengthen(f, m, debug=debug)
    wrapped = wrapper(strengthen, f, m, debug)
    stren_time = timeit.timeit(wrapped, number=1)
    print("f is: " + str(f))
    print("f after strengthening:")
    print(r)
    print(f"time to strengthen f: {stren_time}")


def read_smt2(filename):
    formula = parse_smt2_file(filename)
    if is_and(formula):
        return formula.children()
    else:
        return formula


def built_in_tests():
    x = Int("x")
    y = Int("y")
    z = Int("z")
    t = Int("t")
    f = And(((x + y) * (x + 1) <= 8), (y <= 2), (x + z > 3))
    strengthen_formula_test(f)
    f = (x > 0)
    strengthen_formula_test(f)
    f = Implies(And(Not(If(x > 0, y < 0, y > 0)), Or(z <= 7, x <= 8)), y == 2)
    strengthen_formula_test(f)
    f = And(x > 0, And(y < 0, x >= 7))
    strengthen_formula_test(f)
    f = And(x <= 0, y + z <= 7)
    strengthen_formula_test(f)
    f = And(x > 0, x - t <= 3, 5 * y >= 4, y + z <= 7, z == 5, t != 4)
    strengthen_formula_test(f)
    f = And(-7 * z + 2 * t - 6 * y != 5)
    strengthen_formula_test(f)


if __name__ == "__main__":
    sys_args = _sys.argv[1:]
    if len(sys_args) == 0:
        print("No files were given. Running built-in tests.")
        built_in_tests()
    for file in sys_args:
        print(f"reading from file: {file}")
        constraints = read_smt2(file) # file-error handling is done inside read_smt2
        f = And(constraints)
        strengthen_formula_test(f)
