#!/usr/bin/env python3

import argparse
import cProfile, pstats, io
from pstats import SortKey
from dpll import CDCL


def parseArg():
    """
    CMD argument parsing
    :return: the parser
    """
    parser = argparse.ArgumentParser(description='SAT solver')
    parser.add_argument('infile')
    parser.add_argument('--profile')
    return parser


def parse_input(f):
    with open(f,'r') as f:
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
    if args.profile:
        pr = cProfile.Profile()
        pr.enable()
    
    cnf = CDCL(n_vars, nss, "dpll.log")

    if args.profile:
        pr.disable()
        s = io.StringIO()
        sortby = SortKey.TIME
        ps = pstats.Stats(pr, stream=s).strip_dirs().sort_stats(sortby)
        ps.print_stats(40)
        if args.profile == '-':
            print(s.getvalue())
        else:
            with open(args.profile, "w") as outfile:
                outfile.write(s.getvalue())
    else:
        if cnf.sat:
            print("sat")
        else:
            print("unsat")