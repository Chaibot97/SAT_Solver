#!/usr/bin/env python3

import argparse


def parseArg():
    """
    CMD argument parsing
    :return: the parser
    """
    parser = argparse.ArgumentParser(description='SAT solver')
    parser.add_argument('infile', nargs='?', type=argparse.FileType('r'))
    return parser


class SATProblem:
    def __init__(self, n_vars, n_clauses):
        self.vars = [x for x in range(n_vars)]
        self.n_clauses = n_clauses
        self.caluses = []

    def add_clasuse(self, vars):
        self.caluses.append((Clause(vars)))

    def __str__(self):
        res = ""
        for c in self.caluses:
            res += str(c) + '\n'
        return res


class Clause:
    def __init__(self, vars):
        self.neg = []
        self.vars = []
        for v in vars:
            if v[0] == '-':
                self.neg.append(True)
                self.vars.append(int(v[1:]))
            else:
                self.neg.append(False)
                self.vars.append(int(v))

    def __str__(self):
        res = ""
        for i, v in enumerate(self.vars):
            if self.neg[i]:
                res += '-'
            res += str(v) + ' '
        return res


def parse_input(f):
    prob = None
    for line in f:
        line = line.strip()
        if line[0] == 'c':
            continue
        if line[0] == 'p':
            vars = line.split()
            prob = SATProblem(int(vars[2]),int(vars[3]))
            continue
        if prob:
            prob.add_clasuse(line.split())
    return prob


def run():
    args = parseArg().parse_args()
    problem = parse_input(args.infile)
    print(problem)


if __name__ == '__main__':
    run()