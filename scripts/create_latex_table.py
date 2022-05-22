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


def display(i):
    bold, v = i
    ret = "" if not bold else r"\textbf "
    if isinstance(v, fractions.Fraction):
        return f"{ret}{{{float(v)*100:>8.2f}}}"
    return f"{ret}{{{round(v):>8}}}"

#def short_name(x):
#    return x.split("_")[-1][8:16]

def short_name(x):
    return x.split("/")[0]

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
            collections.defaultdict, functools.partial(
                collections.defaultdict, list)))

    totals = collections.defaultdict(list)
    benchmark_count = collections.defaultdict(int)

    for formula in args.formula.glob('**/*.smt2'):
        single = formula.relative_to(args.formula)
        jsons = [ (sample_dir.joinpath(single.with_suffix('.smt2.json')),
                   sample_dir, )
                  for sample_dir in args.samples
                  if sample_dir.joinpath(single.with_suffix('.smt2.json')).is_file() ]
        if len(jsons) != len(args.samples):
            continue
        

        formula_dir = single.parent
        d = store[formula_dir]
        benchmark_count[formula_dir] += 1

        for json_filename, cat in jsons:
            with open(json_filename) as json_file:
                summary = json.load(json_file)

            d["d_epochs"][cat].append(summary["epochs"])
            d["b_depth"][cat].append(summary["formula stats"]["formula AST depth"])
            d["a_ints"][cat].append(summary["formula stats"]["num ints"] + summary["formula stats"]["num arrays"] + summary["formula stats"]["num bools"])
            d["f_solutions"][cat].append(summary["unique valid samples"])
            d["c_coverage"][cat].append(fractions.Fraction(summary.get("wire_coverage", 0)))
            d["e_smtcalls"][cat].append(summary["maxsmt calls"])

            totals[f"coverage_{short_name(cat.name)}"].append(d["c_coverage"][cat][-1])
            totals[f"solutions_{short_name(cat.name)}"].append(d["f_solutions"][cat][-1])


    megamax_coverages = []
    for benchmark in store:
        mega = store[benchmark]["c_coverage"][args.samples[0]]
        megab = store[benchmark]["c_coverage"][args.samples[1]]
        for a, b in zip(mega, megab):
            print(a, b)
            megamax_coverages.append(max(a, b))

    totals[f"coverage_megasampler"] = megamax_coverages
    totals[f"solutions_megasampler"] = totals[f"solutions_{short_name(args.samples[0].name)}"] + totals[f"solutions_{short_name(args.samples[1].name)}"]

    for key in totals:
        totals[key] = statistics.mean(totals[key])

    store2 = {}
    for benchmark in store:
        store2[benchmark] = {}
        for column in store[benchmark]:
            top = 0
            for cat in store[benchmark][column]:
                print(f"{short_name(cat.name)}")
                if column == 'e_smtcalls' and cat != args.samples[-1]:
                    continue
                value = statistics.mean(store[benchmark][column][cat])
                top = max(value, top)
                store2[benchmark][f"{column}_{short_name(cat.name)}"] = value
            for cat in store[benchmark][column]:
                if column == 'e_smtcalls' and cat != args.samples[-1]:
                    continue
                value = store2[benchmark][f"{column}_{short_name(cat.name)}"] 
                assert(not isinstance(value, tuple))
                if value == top:
                    value = (True, value)
                else:
                    value = (False, value)
                store2[benchmark][f"{column}_{short_name(cat.name)}"] = value

    for benchmark in store2:
        depth = -1
        ints = -1
        # It's horrible but I'm tired just do it the stupid way
        for key in list(store2[benchmark].keys()):
            if not key.startswith("b_depth"):
                continue
            if depth != -1:
                assert(depth == store2[benchmark][key][1])
            depth = store2[benchmark][key][1]
            del store2[benchmark][key]
        for key in list(store2[benchmark].keys()):
            if not key.startswith("a_ints"):
                continue
            if ints != -1:
                assert(ints == store2[benchmark][key][1])
            ints = store2[benchmark][key][1]
            del store2[benchmark][key]
        for key in store2[benchmark]:
            if key.startswith('e_smtcalls'):
                store2[benchmark][key] = (False, store2[benchmark][key][1])
        store2[benchmark]["a_ints"] = (False, ints)
        store2[benchmark]["b_depth"] = (False, depth)

    n = max(len(store2[x]) for x in store2)

    print("% benchmark " + " ".join((sorted(store2[list(store2.keys())[-1]]))))
    for benchmark in sorted(store2):
        if len(store2[benchmark]) < n:
            continue
        data = " & ".join(display(store2[benchmark][key]) for key in sorted(store2[benchmark].keys()))
        quoted = str(benchmark)
        if 'Bromberger' in quoted:
            quoted = quoted.replace(r"20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt", r"CAV2009-slacked\tnote{1}\;\,")
            quoted = quoted.replace(r"20180326-Bromberger/unbd-sage/unbd010v15c", r"unbd-sage\tnote{2}\;\,")
        elif 'random' in quoted:
            quoted = quoted.replace(r"bofill-scheduling/SMT_random_LIA", r"bofill-sched-random\tnote{4}\;\,")
        elif 'real' in quoted:
            quoted = quoted.replace(r"bofill-scheduling/SMT_real_LIA", r"bofill-sched-real\tnote{5}\;\,")
        else:
            quoted = quoted.replace(r"CAV_2009_benchmarks/smt", r"CAV2009\tnote{3}\;\,")
        quoted = quoted.replace('_', r'\_')
        print(f"{quoted: <50} & {data} \\\\")
    print("% " + " ".join(f"{key}={float(value)}" for key, value in totals.items()))
        

if __name__ == '__main__':
    main()
