from z3_utils import *
import sys as _sys
from formula_strengthener import strengthen
from interval import Interval, IntervalSet, INF, MINF


def timed(func):
    def func_wrapper(*args, **kwargs):
        from datetime import datetime
        s = datetime.now()
        result = func(*args, **kwargs)
        e = datetime.now()
        return result, e-s
    return func_wrapper


def solve_and_strengthen_formula(f, debug = False):
    print("f is: " + str(f))
    s = Solver()
    s.add(f)
    s.check()
    m = s.model()
    r, stren_time = timed(strengthen)(f, m, debug)
    print("f after strengthening:")
    print(r)
    print(f"time to strengthen f: {stren_time.total_seconds()}s")
    return r


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
    b = Bool("b")
    f = (x * y >= 60)
    r = solve_and_strengthen_formula(f, True)
    assert not r.unsimplified_demands
    # # I_1 == IntervalSet({"x": Interval(3, 4), "y": Interval(-3, -2), "z": Interval(3,4)})
    # I = IntervalSet({"x": Interval(60, INF), "y": Interval(1, INF)})
    # assert r.interval_set == I
    f = (x % y == 4)
    r = solve_and_strengthen_formula(f, True)
    assert not r.unsimplified_demands
    f = (x % y >= 4)
    r = solve_and_strengthen_formula(f, True)
    assert r.unsimplified_demands
    f = (x * y * z >= 70)
    solve_and_strengthen_formula(f, True)
    f = And(x * y * z >= 70, y==-1, z==-1)
    solve_and_strengthen_formula(f, True)
    f = And(x * y * z >= -70, y==1, z==-1)
    solve_and_strengthen_formula(f, True)
    f = And(x * y * 4 * z >= -70, y==1, z==-1)
    solve_and_strengthen_formula(f, True)
    f = And(x * y * 4 * z >= -70, x + 3*y <= 9)
    solve_and_strengthen_formula(f, True)
    f = And(((x + y) * (x + 1) <= 8), (y <= 2), (x + z > 3))
    solve_and_strengthen_formula(f, True)
    f = Or(Not(b), x>8)
    solve_and_strengthen_formula(f, True)
    f = (x > 0)
    solve_and_strengthen_formula(f, True)
    f = Implies(And(Not(If(x > 0, y < 0, y > 0)), Or(z <= 7, x <= 8)), y == 2)
    solve_and_strengthen_formula(f, True)
    f = And(x > 0, And(y < 0, x >= 7))
    solve_and_strengthen_formula(f, True)
    f = And(x <= 0, y + z <= 7)
    solve_and_strengthen_formula(f, True)
    f = And(x > 0, x - t <= 3, 5 * y >= 4, y + z <= 7, z == 5, t != 4)
    solve_and_strengthen_formula(f, True)
    f = And(-7 * z + 2 * t - 6 * y != 5)
    solve_and_strengthen_formula(f, True)


if __name__ == "__main__":
    sys_args = _sys.argv[1:]
    if len(sys_args) == 0:
        print("No files were given. Running built-in tests.")
        built_in_tests()
    for file in sys_args:
        print(f"reading from file: {file}")
        constraints = read_smt2(file) # file-error handling is done inside read_smt2
        f = And(constraints)
        solve_and_strengthen_formula(f)
