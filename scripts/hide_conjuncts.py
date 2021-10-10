"""
Script to generate sub-benchmarks with less conjuncts.
"""
import itertools
import sys
import random

import z3
from z3 import z3util

OUTPUT_SIZE = 8
RANDOM_SEED = "A man, a plan, a canal: Panama!"


def toSMT2Benchmark(f, status="sat", name="benchmark", logic=""):
    v = (z3.Ast * 0)()
    return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status,
                                            "", 0, v, f.as_ast())


def backtrack_permutations(conjuncts, all_vars, ctx):
    stack = []
    indexed = dict(enumerate(conjuncts))
    expr_vars = {
        i: [str(x) for x in z3util.get_vars(v)]
        for i, v in indexed.items()
    }

    def have_all_vars(exprs):
        s = set()
        for expr in exprs:
            s.update(expr_vars[expr])
            if len(s) == len(all_vars):
                return True
        return False

    stack.append(range(len(indexed)))

    while stack:  # is not empty
        es = stack.pop()

        # ignore if empty
        if not es:
            continue

        # ignore if not all vars are present
        if not have_all_vars(es):
            continue

        # yield solution (skip the full formula...)!
        if len(es) != len(conjuncts):
            yield [indexed[e] for e in es]

        # add candidates
        for e in es:
            # don't remove conjuncts with only 1 var, like 'x >= 1'
            if len(expr_vars[e]) < 2:
                continue
            stack.append([f for f in es if e > f])


def main(filename):
    c = z3.Context()

    inp = z3.parse_smt2_file(filename, ctx=c)
    g = z3.Goal(ctx=c)
    remaining = list(inp)
    while remaining:
        term = remaining.pop()
        if z3.is_and(term):
            remaining.extend(term.children())
        else:
            g.add(term)

    t = z3.Then('simplify', 'solve-eqs', 'nnf', ctx=c)
    simplified = t(g).as_expr()

    if not z3.is_and(simplified):
        print(f"{filename}: Expr is not a conjunction")
        sys.exit(1)

    all_vars = sorted(z3util.get_vars(simplified), key=str)

    print(f"Starting, formula has {len(simplified.children())} conjuncts.")

    size = sum(1 for _ in backtrack_permutations(
        simplified.children(), all_vars, ctx=c))
    print(f"There are {size} possible formulas")

    random.seed(RANDOM_SEED)
    selected_outputs = random.sample(range(size), k=min(size, OUTPUT_SIZE))
    outputs = list(
        itertools.islice((x for i, x in enumerate(
            backtrack_permutations(simplified.children(), all_vars, ctx=c))
                          if i in selected_outputs), len(selected_outputs)))

    benchmarks = [
        toSMT2Benchmark(z3.And(*output),
                        name=f"Based on {filename}, variation #{i+1}",
                        logic="QF_LIA") for i, output in enumerate(outputs)
    ]
    for benchmark in benchmarks:
        print(benchmark)


if __name__ == '__main__':
    main(*sys.argv[1:])
