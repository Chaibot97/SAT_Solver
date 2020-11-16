#!/usr/bin/env python3
from lark import Lark, Transformer
from fractions import Fraction
import argparse
import sys
from math import floor, ceil
from copy import deepcopy
from collections import deque

AUX = 'aux'  # variable used in L_aux
POS = 'pos'  # variable used in phase 2 to ensure positivity


# parser
def formula_parser():
    grammar = """
        formula : "AND" "(" atom ("," atom)* ")" -> formula
        atom : term OP term   -> atom
        term : term "+" term        -> plus
            | term "-" term         -> minus
            | RATIONAL "*" VAR      -> times
            | RATIONAL              -> number
            | VAR                   -> var

        RATIONAL : SIGNED_NUMBER ["/" NUMBER]
        OP :  ">=" | "<=" | "<" | ">"
        VAR : /[a-zA-Z][a-zA-Z0-9]*/

        %import common.SIGNED_NUMBER
        %import common.NUMBER
        %import common.WS
        %ignore WS
        """

    return Lark(grammar, start="formula")


# transformer for parser (to Object)
class FormulaTransformer(Transformer):
    def number(self, n):
        (n,) = n
        return Term(n, 1)

    def var(self, x):
        (x,) = x
        return Term(1, x)

    def times(self, args):
        return Term(args[0], args[1])

    def minus(self, args):
        return args[0] - args[1]

    def plus(self, args):
        return args[0] + args[1]

    def atom(self, args):
        return Atom(args[0], args[2], args[1])

    def formula(self, args):
        return Formula(args)


class Opti:
    def __init__(self, formula):
        self.obj_fun = Term()
        self.formula = formula
        self.vars = {}
        for x in sorted(formula.get_vars()):
            self.vars[x] = x
        self.value = 'v'

    def __str__(self):
        vertices = ', '.join([str(self.vars[k]) for k in sorted(self.vars.keys())])
        return 'OPT({}, {}, ({}), {})'.format(self.obj_fun, self.formula, vertices, self.value)

    def evaluate(self):
        atoms = self.formula.atoms
        for a in atoms:
            nb = a.non_basic()
            b = list(a.basic())[0]
            for x in nb:
                self.vars[x] = 0
            self.vars[b] = a.evaluate(self.vars)
        self.value = self.obj_fun.evaluate(self.vars)

    def get_res(self):
        res = {}
        for x in self.formula.targets:
            x_f, x_ff = x + '_f', x + '_ff'
            new_term = Term(1, x_f) - Term(1, x_ff)
            res[x] = new_term.evaluate(self.vars)
        return res

    def union_atom(self, a):
        new_formula = self.formula.union_atom(a)
        new_prob = Opti(new_formula)
        new_prob.obj_fun = self.obj_fun
        new_prob.vars = self.vars
        new_prob.value = self.value
        return new_prob

    def simplex(self):
        sat = False
        if self.simplex_phase_1():
            if self.formula.has_strict_ineq:
                if self.simplex_phase_2():
                    sat = True
            else:  # if there's no strict inequality, SAT since P1 succeeded
                sat = True
        if sat:
            res = []
            for x in self.formula.targets:
                x_f, x_ff = x + '_f', x + '_ff'
                new_term = Term(1, x_f) - Term(1, x_ff)
                res.append('{}={}'.format(x, new_term.evaluate(self.vars)))
        else:
            res = ['UNSAT']
        return '\n'.join(res)

    def simplex_phase_1(self):
        """Phase 1 of simplex"""
        self.obj_fun = Term(-1, AUX)  # maximize -aux
        print(self)

        atoms = self.formula.atoms
        # basic solution already feasible if each eqn's constant is >= 0
        if min([a.get_coeff_of(1) for a in atoms]) >= 0:
            pass
        else:  # some eqn contains negative constant, but can get feasible after 1 pivot
            # find the eqn with the most negative constant
            # equivalently, find one that constrains aux the least,
            # since aux's coeff = 1
            min_index = -1
            min_constrain = float('inf')
            for i, a in enumerate(atoms):
                cons = a.constrain(AUX)
                if cons < min_constrain:
                    min_index = i
                    min_constrain = cons
            # make aux basic and perform necessary substitutions
            tmp = atoms[min_index].represent(AUX)
            for i, _ in enumerate(atoms):
                if i != min_index:
                    atoms[i].substitute(AUX, tmp)
            self.obj_fun.substitute(AUX, tmp)

        self.simplex_recursive()
        return self.value == 0

    def simplex_phase_2(self):
        self.obj_fun = Term(1, POS)  # maximize positivity margin
        # fist, we need to get rid of x0 from phase 1
        # check if aux is basic
        aux_basic = [(i, eqn) for i, eqn in enumerate(self.formula.atoms) if AUX in eqn.basic()]
        # if aux is basic, then we have
        #   aux = 0 = a_1 x_1 + ... (*), where x_i are non-basic.
        # (We know aux = 0 since phase 1 succeeded, and c = 0 since the solution is basic)
        if len(aux_basic) > 0:
            i, eqn = aux_basic[0]  # there should be only 1 such eqn
            # if there is some a_i at all, make x_i basic
            x_i = None
            for x_i, a_i in eqn.tr.vars.items():
                if a_i != 0:
                    break
            if x_i is not None:
                new = eqn.represent(x_i)
                new.substitute(AUX, Term(0))  # set aux to 0
                for j, eqn in enumerate(self.formula.atoms):
                    if i != j:
                        self.formula.atoms[j].substitute(x_i, new)
                self.obj_fun.substitute(x_i, new)
            # else, we have the trivial eqn aux = 0, so delete this one
            else:
                self.formula.atoms.remove(i)
        # else, aux is non basic, so just set aux = 0 in every eqn
        else:
            for eqn in self.formula.atoms:
                eqn.substitute(AUX, Term(0))
        self.simplex_recursive()
        return self.value > 0

    def simplex_recursive(self):
        self.evaluate()
        print(self)
        pos_terms = self.obj_fun.get_positive_terms()
        if len(pos_terms) == 0:
            return

        atoms = self.formula.atoms
        for x in sorted(pos_terms):  # bland's rule?
            if min([a.get_coeff_of(x) for a in atoms]) >= 0:
                # x unbounded, so we can always make objective > 0
                if self.obj_fun.c <= 0:
                    x_val = Term(-self.obj_fun.c + 1)  # makes obj = 1
                else:
                    x_val = Term(0)  # obj already > 0
                # Make x basic and set x = x_val
                for i in range(len(atoms)):
                    atoms[i].substitute(x, x_val)
                self.obj_fun.substitute(x, x_val)
                atoms.append(Atom(Term(1, x), x_val, '='))
                self.evaluate()
                return

            min_index = -1
            min_constrain = float('inf')
            for i, a in enumerate(atoms):
                if a.get_coeff_of(x) > 0:
                    continue
                cons = -a.constrain(x)
                if 0 <= cons < min_constrain:
                    min_index = i
                    min_constrain = cons

            if min_index != -1:
                tmp = atoms[min_index].represent(x)
                for i in range(len(atoms)):
                    if i != min_index:
                        atoms[i].substitute(x, tmp)
                self.obj_fun.substitute(x, tmp)

                return self.simplex_recursive()


class Formula:
    def __init__(self, atoms):
        self.atoms = []
        targets = set()
        self.has_strict_ineq = False
        for i, a in enumerate(atoms):
            a.clear_negation()
            a.to_slack(i + 1)
            self.atoms.append(a)
            targets = targets.union(a.targets)
            self.has_strict_ineq = self.has_strict_ineq or a.ineq

        # list of original vars in the input
        self.targets = {}
        for t in targets:
            self.targets[t] = Term(1, t)

    def union_atom(self, a):
        # for branch and bound
        new_formula = deepcopy(self)
        i = len(self.atoms)
        a.clear_negation()
        a.to_slack(i + 1)
        new_formula.atoms.append(a)
        return new_formula

    def get_vars(self):
        result = set()
        for a in self.atoms:
            result = result.union(a.get_vars())
        return result

    def __str__(self):
        string = 'AND('
        for a in self.atoms:
            string += '{}, '.format(a)
        string = string[:-2] + ')'
        return string


class Atom:
    def __init__(self, tl, tr, op):
        self.tl = tl
        self.tr = tr
        self.op = op
        self.targets = self.get_vars()
        self.ineq = False
        if op == '<' or op == '>':
            self.ineq = True  # contain < or >

    def non_basic(self):
        return self.tr.get_vars()

    def basic(self):
        return self.tl.get_vars()

    def evaluate(self, vars):
        return self.tr.evaluate(vars)

    def represent(self, var):
        old_coeff = self.tr.remove(var)
        self.tr -= self.tl
        self.tr = self.tr.mul(1 / -old_coeff)
        self.tl = Term(1, var)
        return self.tr

    def substitute(self, old, new):
        self.tr.substitute(old, new)

    def get_coeff_of(self, var):
        return self.tr.get_coeff_of(var)

    def constrain(self, var):
        return self.tr.constrain(var)

    def get_vars(self):
        result = set()
        result = result.union(self.tl.get_vars())
        result = result.union(self.tr.get_vars())
        return result

    def clear_negation(self):
        for x in sorted(self.targets):
            x_f, x_ff = x + '_f', x + '_ff'
            new_term = Term(1, x_f) - Term(1, x_ff)
            self.tl.substitute(x, new_term)
            self.tr.substitute(x, new_term)

    def to_slack(self, index):
        # index of the slack var
        if self.op == '=':
            return
        slack = Term(1, 's' + str(index))
        if self.op == '<=':
            self.tr = self.tr - self.tl
            self.tl = slack
        elif self.op == '>=':
            self.tr = self.tl - self.tr
            self.tl = slack
        elif self.op == '<':
            self.tl += Term(1, POS)
            self.tr = self.tr - self.tl
            self.tl = slack
        elif self.op == '>':
            self.tr += Term(1, POS)
            self.tr = self.tl - self.tr
            self.tl = slack

        self.tr += Term(1, AUX)
        self.op = '='

    def __str__(self):
        return '{} {} {}'.format(str(self.tl), self.op, str(self.tr))


class Term:
    def __init__(self, coeff=0, var='1'):
        coeff = Fraction(coeff)
        var = str(var)
        self.vars = {}
        self.c = 0
        if var == '1':
            self.c = coeff
        else:
            self.vars[var] = coeff

    def constrain(self, var):
        if var not in self.vars or self.vars[var] == 0:
            return float('inf')
        return self.c / self.vars[var]

    def remove(self, var):
        # remove a term and return its coefficient
        coeff = self.vars[var]
        self.vars.pop(var)
        return coeff

    def get_coeff_of(self, var):
        if var == 1:
            return self.c
        if var not in self.vars:
            return 0
        return self.vars[var]

    def get_positive_terms(self):
        return [v for v in self.vars if self.vars[v] > 0]

    def get_vars(self):
        return set(self.vars.keys())

    def evaluate(self, vars):
        # vars and corresponding values
        sum = self.c
        for x in self.vars:
            sum += self.vars[x] * vars[x]
        return sum

    def substitute(self, old, new):
        """
        :param old: old var string
        :param new: new term
        """
        if old not in self.vars:
            return
        old_coeff = self.vars[old]
        self.vars.pop(old)
        tmp = Term()
        tmp = self + new.mul(old_coeff)
        self.vars = tmp.vars
        self.c = tmp.c

    def mul(self, c):
        tmp = Term()
        tmp.c = self.c * c
        for v in self.vars:
            tmp.vars[v] = self.vars[v] * c
        return tmp

    def __add__(self, o):
        tmp = Term()
        tmp.vars = self.vars.copy()
        tmp.c = self.c + o.c
        for v in o.vars:
            if v in tmp.vars:
                tmp.vars[v] += o.vars[v]
            else:
                tmp.vars[v] = o.vars[v]
        return tmp

    def __sub__(self, o):
        tmp = Term()
        tmp.vars = self.vars.copy()
        tmp.c = self.c - o.c
        for v in o.vars:
            if v in tmp.vars:
                tmp.vars[v] -= o.vars[v]
            else:
                tmp.vars[v] = -o.vars[v]
        return tmp

    def __str__(self):
        string = ""
        if self.c != 0:
            string += str(self.c) + ' + '
        for v in sorted(self.vars):
            coeff = self.vars[v]
            if coeff == 1:
                string += '{} + '.format(v)
            elif coeff == -1:
                string += '-{} + '.format(v)
            elif coeff != 0:
                string += '{} * {} + '.format(str(coeff), v)
        return string[:-3]


def run(inp, integer=False):
    parser = formula_parser()
    par_tree = parser.parse(inp)
    formula = FormulaTransformer().transform(par_tree)
    lp = Opti(formula)
    if integer:
        return branch_and_bound(lp)
    else:
        return lp.simplex()


def branch_and_bound(s):
    q = deque()
    q.append(s)
    res = search_integral_solution(q)
    return res


def search_integral_solution(q):
    s = q.popleft()
    old_s = deepcopy(s)
    res = s.simplex()
    if res == 'UNSAT':
        return 'UNSAT'
    else:
        vals = s.get_res()
        v = None
        r = 0
        for x in vals:
            r = vals[x]
            if r != int(r):
                v = x
                break
        if not v:
            return res
        else:
            prob1 = old_s.union_atom(Atom(Term(1, v), Term(floor(r), '1'), '<='))
            prob2 = old_s.union_atom(Atom(Term(1, v), Term(ceil(r), '1'), '>='))
            q.append(prob1)
            q.append(prob2)
            return search_integral_solution(q)


def parseArg():
    """
    CMD argument parsing
    :return: the parser
    """
    parser = argparse.ArgumentParser(description='Simplex inequality solver')
    parser.add_argument('infile', nargs='?', type=argparse.FileType('r'), default=sys.stdin)
    parser.add_argument('--integer', '-i', action='store_true')
    return parser


if __name__ == "__main__":
    args = parseArg().parse_args()
    inp = args.infile.readline()
    res = run(inp, args.integer)
    print(res)
