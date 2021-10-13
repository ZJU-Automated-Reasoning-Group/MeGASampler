import argparse
import copy
import glob
import json
import pathlib
import sys

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


def main():
    args = PARSER.parse_args(sys.argv[1:])

    for sample in args.samples:
        if not sample.is_dir():
            PARSER.error(f"{sample} is not a directory.")

    if not args.formula.is_dir():
        PARSER.error(f"{formula} is not a directory.")

    for formula_file in glob.glob(f"{args.formula}/**/*.smt2"):
        formula_file = formula_file.relative_to(args.formula)
        files = [(sample_dir.joinpath(formula_file, '.json'),
                  sample_dir.joinpath(formula_file, '.samples'))
                 for sample_dir in args.samples
                 if sample_dir.joinpath(formula_file, '.json').is_file()]
        if not json_files:
            continue
        with open(formula_file) as formula:
            metric = calc_metric.ManualSatisfiesMetric(
                formula_file.read(),
                statistics=calc_metric.WireCoverageStatistics())
        statistics_template = copy.deepcopy(metric._statistics)
        for json_file, samples_file in files:
            metric._statistics = copy.deepcopy(statistics_template)
            with open(samples_file) as sf:
                for s in calc_metric.parse_samples(sf):
                    metric.count_sample(sample)
                result = metric.result
            with open(json_file) as jf:
                summary = json.load(jf)
            summary["wire_coverage"] = str(result)
            summary["wire_coverage_denom"] = result.denominator
            summary["wire_coverage_numer"] = result.numerator
            with open(json_file, 'w') as jf:
                json.dump(summary, jf)
        print(f"{formula_file}: {len(files}} JSONs updated")


if __name__ == '__main__':
    main()
