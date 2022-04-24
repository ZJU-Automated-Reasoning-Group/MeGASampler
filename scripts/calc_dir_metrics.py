import argparse
import copy
import functools
import json
import multiprocessing
import pathlib
import sys
import typing as typ

import calc_metric

PARSER = argparse.ArgumentParser(description="calc_metric.py on whole dir")
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


def process_single_formula(formula_file, args):
    formula_file = formula_file.relative_to(args.formula)
    files = [(sample_dir.joinpath(formula_file.with_suffix('.smt2.json')),
              sample_dir.joinpath(formula_file.with_suffix('.smt2.samples')))
             for sample_dir in args.samples
             if sample_dir.joinpath(formula_file.with_suffix('.smt2.json')).is_file()]
    if not files:
        return
    with open(args.formula.joinpath(formula_file)) as formula:
        try:
            metric = calc_metric.ManualSatisfiesMetric(
                formula.read(),
                statistics=calc_metric.WireCoverageStatistics())
        except Exception as e:
            import traceback
            traceback.print_exc()
            print(f"Failed to process {formula_file}")
            return
    statistics_template = copy.deepcopy(metric._statistics)
    statistics: typ.Mapping[str, WireCoverageStatistics] = {}
    for json_file, samples_file in files:
        metric._statistics = copy.deepcopy(statistics_template)
        statistics[json_file] = metric._statistics
        with open(samples_file) as sf:
            for s in calc_metric.parse_samples(sf):
                try:
                    metric.count_sample(s)
                except Exception as e:
                    import traceback
                    traceback.print_exc()
                    print(f"Failed to process {formula_file} -- {samples_file}")
                    return

    totals = calc_metric.WireCoverageStatistics.union_totals(*statistics.values())
    for s in statistics.values():
        s.set_totals(totals)

    for json_file, _ in files:
        with open(json_file) as jf:
            summary = json.load(jf)

        metric._statistics = statistics[json_file]
        result = metric.result
        summary["wire_coverage"] = str(result)
        summary["wire_coverage_denom"] = result.denominator
        summary["wire_coverage_numer"] = result.numerator
        with open(json_file, 'w') as jf:
            json.dump(summary, jf)
    print(f"{formula_file}: {len(files)} JSONs updated")


def main():
    sys.setrecursionlimit(10500) # need a bit more
    args = PARSER.parse_args(sys.argv[1:])

    for sample in args.samples:
        if not sample.is_dir():
            PARSER.error(f"{sample} is not a directory.")

    if not args.formula.is_dir():
        PARSER.error(f"{formula} is not a directory.")

    pool = multiprocessing.Pool()
    pool.map(functools.partial(process_single_formula, args=args), args.formula.glob('**/*.smt2'))


if __name__ == '__main__':
    main()
