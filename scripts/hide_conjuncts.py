"""
Script to generate sub-benchmarks with less conjuncts.
"""
import itertools
import sys
import random

import z3
import z3.z3util

MAX_DROP = 1
OUTPUT_SIZE = 8
RANDOM_SEED = "A man, a plan, a canal: Panama!"


def toSMT2Benchmark(f, status="sat", name="benchmark", logic=""):
    v = (z3.Ast * 0)()
    return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status,
                                            "", 0, v, f.as_ast())


def partition(l, condition):
    good, bad = [], []
    for x in l:
        (bad, good)[condition(x)].append(x)
    return good, bad

def backtrack_subsets(conjuncts, all_vars, ctx=None):
    size = len(conjuncts)
    expr_vars = {
        i: [str(x) for x in z3.z3util.get_vars(v)]
        for i, v in enumerate(conjuncts)
    }

    def have_all_vars(exprs):
        s = set()
        for expr in exprs:
            s.update(expr_vars[expr])
            if len(s) == len(all_vars):
                return True
        return False

    always, sometimes = partition(range(size), lambda c: len(expr_vars[c]) < 2)

    for selected in itertools.product([0,1], repeat=len(sometimes)):
        indexes = always + [ sometimes[i] for i, pred in enumerate(selected)
                             if pred == 1 ]
        if have_all_vars(indexes):
            yield [ conjuncts[i] for i in indexes ]

def load_formula(filename):
    inp = z3.parse_smt2_file(filename)
    g = z3.Goal()
    remaining = list(inp)
    while remaining:
        term = remaining.pop()
        if z3.is_and(term):
            remaining.extend(term.children())
        else:
            g.add(term)

    t = z3.Then('simplify', 'solve-eqs', 'nnf')
    simplified = t(g).as_expr()

    if not z3.is_and(simplified):
        print(f"{filename}: Expr is not a conjunction")

    all_vars = sorted(z3.z3util.get_vars(simplified), key=str)

    return simplified.children(), all_vars


def main(filename):
    conjuncts, all_vars = load_formula(filename)

    def get_it():
        return ( f for f in backtrack_subsets(conjuncts, all_vars)
                 if len(f) >= len(conjuncts) - MAX_DROP)
    
    print(f"Starting, formula has {len(conjuncts)} conjuncts.")

    size = sum(1 for _ in get_it())
    print(f"There are {size} possible formulas")

    random.seed(RANDOM_SEED)
    selected_outputs = random.sample(range(size), k=min(size, OUTPUT_SIZE))
    outputs = [ f for i, f in enumerate(get_it())
                if i in selected_outputs ]
    
    benchmarks = [
        toSMT2Benchmark(z3.And(*output),
                        name=f"Based on {filename}, variation #{i+1}",
                        logic="QF_LIA") for i, output in enumerate(outputs)
    ]
    for i, benchmark in enumerate(benchmarks):
        with open(f"{filename}.subset{i}.smt2", "w") as f:
            f.write(benchmark)


if __name__ == '__main__':
    main(*sys.argv[1:])
