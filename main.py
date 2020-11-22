#!/usr/bin/env python3

import argparse
from dpll import CDCL


def parseArg():
    """
    CMD argument parsing
    :return: the parser
    """
    parser = argparse.ArgumentParser(description='SAT solver')
    parser.add_argument('infile', nargs='?', type=argparse.FileType('r'))
    return parser


def parse_input(f):
    nss = []
    for line in f:
        line = line.strip()
        if line[0] == 'c':
            pass
        elif line[0] == 'p':
            _, _, n_vars, _ = line.split()
        else:
            ns = [int(n) for n in line.split() if n != '0']
            nss.append(ns)
    return int(n_vars), nss


if __name__ == '__main__':
    args = parseArg().parse_args()
    n_vars, nss = parse_input(args.infile)
    cnf = CDCL(n_vars, nss)
    if cnf.run():
        print("sat")
    else:
        print("unsat")