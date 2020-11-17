#!/usr/bin/env python3

import argparse
import dpll


def parseArg():
    """
    CMD argument parsing
    :return: the parser
    """
    parser = argparse.ArgumentParser(description='SAT solver')
    parser.add_argument('infile', nargs='?', type=argparse.FileType('r'))
    return parser


def parse_input(f):
    cs = []
    for line in f:
        line = line.strip()
        if line[0] == 'c':
            pass
        elif line[0] == 'p':
            _, _, n_vars, _ = line.split()
        else:
            vs = [int(v) for v in line.split() if v != '0']
            cs.append(vs)
    return n_vars, cs


if __name__ == '__main__':
    args = parseArg().parse_args()
    n_vars, cs = parse_input(args.infile)
    cnf = dpll.CNF(int(n_vars), [dpll.Clause(vs) for vs in cs])
    if cnf.dpll():
        print("sat")
    else:
        print("unsat")