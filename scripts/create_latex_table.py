import argparse
import collections
import functools
import fractions
import json
import pathlib
import statistics
import sys

PARSER = argparse.ArgumentParser(description="Evaluate JSONs into LaTeX table")
PARSER.add_argument('-f',
                    '--formula',
                    metavar='DIR',
                    type=pathlib.Path,
                    required=True,
                    help="Formulas basedir")
PARSER.add_argument('-s',
                    '--samples',
                    metavar='DIR',
                    type=pathlib.Path,
                    required=True,
                    action='append',
                    help="Sample basedirs (multiple supported)")


def main():
    args = PARSER.parse_args(sys.argv[1:])

    for sample_dir in args.samples:
        if not sample_dir.is_dir():
            PARSER.error(f"{sample_dir} is not a directory")

    if not args.formula.is_dir():
        PARSER.error(f"{formula} is not a directory.")

    # samples = sorted(args.samples)
    store = collections.defaultdict(
        functools.partial(
            collection.defaultdict, functools.partial(
                collections.defaultdict, list)))

    for formula in args.formula.glob('**/*.smt2'):
        single = formula_file.relative_to(args.formula)
        jsons = [ (sample_dir.joinpath(formula_file.with_suffix('.smt2.json')),
                   sample_dir, )
                  for sample_dir in args.samples
                  if sample_dir.joinpath(formula_file.with_suffix('.smt2.json').is_file()) ]
        if not files:
            return

        formula_dir = single.parent
        d = store[formula_dir]

        for json_filename, cat in jsons:
            with open(json_filename) as json_file:
                summary = json.load(json_file)

            d["epochs"][cat].append(summary["epochs"])
            #d["depth"][cat].append(summary["formula AST depth"])
            d["solutions"][cat].append(summary["unique valid_samples"])
            d["coverage"][cat].append(fractions.Fraction(summary["wire_coverage"]))

    store2 = {}
    for benchmark in store:
        store2[benchmark] = {}
        for column in store[benchmark]:
            for cat in store[benchmark][column]:
                value = statistics.mean(store[benchmark][column][cat])
                store2[benchmark][f"{column}_{cat}"] = value

    for benchmark in store2:
        print(f"{benchmark} {store2[key] for key in sorted(store2[benchmark].keys())}")

if __name__ == '__main__':
    main()
