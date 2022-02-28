#!/usr/bin/env python3
from __future__ import annotations
import argparse
import pathlib
import sys

import z3


PARSER = argparse.ArgumentParser(
    description='Remove array equalities from smt2 files')
PARSER.add_argument('-i',
                    '--input',
                    metavar='FILE',
                    type=pathlib.Path,
                    required=True,
                    help="Input file or base directory with inputs")
PARSER.add_argument('-o',
                    '--output',
                    metavar='FILE',
                    type=pathlib.Path,
                    required=True,
                    help="Output file or output base directory")

CTX = z3.Context()


def walk_ast(expr: z3.ExprRef) -> z3.ExprRef:
    if z3.is_bool(expr):
        if z3.is_eq(expr) and \
           z3.is_array(expr.children()[0]) and z3.is_array(expr.children()[1]):
            return None
        elif z3.is_and(expr) or z3.is_or(expr) or z3.is_not(expr):
            # using expr.decl() doesn't work, the Python API is annoying
            if z3.is_and(expr):
                op = z3.And
            elif z3.is_or(expr):
                op = z3.Or
            elif z3.is_not(expr):
                op = z3.Not
            else:
                raise NotImplementedError("OP is not implemented")

            children = ( walk_ast(child) for child in expr.children() )
            children = [ child for child in children if child is not None ]
            if len(children) == 0 and len(expr.children()) != 0:
                return None
            if len(children) > 0:
                return op(*children)
            else:
                return expr
        else:
            return expr
    else:
        return expr

def handle_file(file_path: pathlib.Path) -> str:
    assert(file_path.is_file())
    solver = z3.Solver(ctx=CTX)
    solver.push()
    with file_path.open('r') as f:
        solver.from_string(f.read())
    expr = z3.And(solver.assertions())
    solver.pop()
    new_expr = walk_ast(expr)
    new_expr = new_expr if new_expr is not None \
        else z3.BoolVal(True) == z3.BoolVal(True)
    solver.add(new_expr)
    return solver.to_smt2()

def write_file(output_path: pathlib.Path, text: str):
    with output_path.open('w') as f:
        f.write(text)

def main():
    args = PARSER.parse_args(sys.argv[1:])

    if args.output.exists():
        PARSER.error(f"{args.output} already exists")
    if not args.output.parent.exists() or not args.output.parent.is_dir():
        PARSER.error(f"{args.output.parent} is not an existing directory")
    args.output.mkdir(parents=False)

    if args.input.is_file():
        new_formula = load_file(args.input)
        write_file(args.output, new_formula)
    elif args.input.is_dir():
        for path in args.input.glob("**/*.smt2"):
            new_formula = handle_file(path)
            subpath = path.relative_to(args.input)
            output_path = args.output / subpath
            output_path.parent.mkdir(parents=True, exist_ok=True)
            write_file(output_path, new_formula)
    else:
        PARSER.error(f"{args.input} is not an existing file or directory")

if __name__ == '__main__':
    main()
