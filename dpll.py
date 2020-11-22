# cython: language_level=3
# cython: profile=False

from collections import defaultdict
from heapq import heappop, heappush
from random import choice, seed

# seed(10)

RESTART_MULTIPLIER = 1

class CDCL:
    def __init__(self, n_vars, nss):
        self.xs = set()
        self.cs0 = list() # includes trivial clauses
        self.cs = list() # non-trivial clauses
        self.watched = defaultdict(list) # map literal l to clauses that are watching l
        self.watches = dict() # map clause l to the two literals being watching
        self.pending = list() # literals for which we need to check watchers during unit-prop
        # restart using Knuth's reluctant doubling sequence
        self.conflict_count = 0
        self.reluctant = (1,1)
        self.reluctant_next = lambda u,v: (u+1,1) if (u & -u == v) else (u,2*v)
        for ns in nss:
            c = Clause(ns)
            self.cs0.append(c)
            if not c.trivial:
                if len(c) == 1:
                    heappush(self.pending, (0, c.get_only(), c))
                else:
                    self.cs.append(c)
                    for x in c.xs():
                        self.xs.add(x)

        self.preprocess()

    
    def preprocess(self):
        """Prepare watched literals"""
        cs_trivial = list()
        for c in self.cs:
            self.watches[c] = list()
            for l in c.start_watching():
                self.watches[c].append(l)
                self.watched[l].append(c)
    
    def run(self):
        self.m = Model()
        # decision level 0 is reserved for implied literals during the first
        # unit prop (before making any decision)
        self.dl = 0
        if self.unit_prop():
            return None # conflict without decision
        
        self.dl = 1
        while True:
            free = self.free_vars()
            if len(free) == 0:
                break
            l = self.branch(free)
            heappush(self.pending, (self.dl, l, None))
            print("{} = {} @ {}".format(l.var, l.is_pos, self.dl))

            conflict = self.unit_prop()
            # print(self.m)
            if conflict:
                self.conflict_count += 1
            while conflict:
                beta = self.analyze(conflict)
                if beta < 0:
                    return None
                else:
                    l = self.m.undo(beta)
                    self.dl = beta
                    if l: # take the other branch
                        self.dl = beta + 1
                        heappush(self.pending, (self.dl, l, l))
                        conflict = self.unit_prop()
                    else: # both branches have been taken
                        conflict = True # forced backtrack
                # print(self.m)
            # print(self.m)
            self.dl += 1
            if self.should_restart():
                self.restart()
        assert(self.modeled_by())
        return self.m

    
    def watch_correct(self):
        assert(all([c in self.watched[l] for (c, ls) in self.watches.items() for l in ls]))
        assert(all([l in self.watches[c] for (l, cs) in self.watched.items() for c in cs]))
        
    
    def unit_prop(self):
        """Attempt to apply unit propagation using the current model. Return a conflict, if any"""

        while len(self.pending) > 0: # exit loop when no more literal is pending
            dl, l0, reason = heappop(self.pending)
            # print("{} <== {}".format(l0, reason if reason else "Guess"))
            if l0 in self.m:
                if not self.m[l0]:
                    self.pending = list()
                    return reason # conflict
                else:
                    continue # inferred literal is consistent with the model
            if reason: # implied
                self.m.commit(l0, dl, reason)
            else: # guessed
                self.m.assign(l0, dl)
            watched_new = list() # unit clauses
            for c in self.watched[-l0]:
                print(" {} || {}".format(c, " ".join(sorted(list(map(str, self.watches[c]))))), end=" => ")
                # c looks for a substitute literal to watch
                l_subst = None
                for l in c:
                    if l not in self.watches[c] and (l not in self.m or self.m[l]):
                        l_subst = l
                        break
                i = self.watches[c].index(-l0)
                if l_subst:
                    self.watched[l_subst].append(c)
                    self.watches[c][i] = l_subst # c's watch list: [l0, other] -> [l_subst, other]
                    print(" ".join(map(str, self.watches[c])))
                # c becomes unit, and implies the only remaining watched literal
                else:
                    watched_new.append(c) # c still watches l0 and the other literal
                    l_other = self.watches[c][1 - i]
                    heappush(self.pending, (self.dl, l_other, c))
                    print("Unit. Pend", l_other)
            print("Pending:", ", ".join([str(t[1]) for t in self.pending]))
            print(self.m)
            # print("", end="")

            self.watched[-l0] = watched_new
        
        return None
    
    def branch(self, free):
        # return Literal(free[0])
        return Literal(choice([-1,1]) * choice(free))

    def free_vars(self):
        """Return the list of free variables (those that are not in model m)"""
        return [x for x in self.xs if not self.m.has_var(x)]
    
    def should_restart(self):
        return self.conflict_count >= self.reluctant[1] * RESTART_MULTIPLIER
    
    def restart(self):
        print("Restart: ", self.conflict_count)
        self.pending = list()
        self.conflict_count = 0
        self.reluctant = self.reluctant_next(*self.reluctant)
        self.m.undo(0)
        self.dl = 1
        # print(self.m)
    
    def analyze(self, conflict):
        """Analyze the conflict and return the level to which to backtrack"""
        # TODO: non-chronological backjump
        return self.dl - 1

    def __str__(self):
        meta = "p cnf {} {}".format(len(self.vs), len(self.cs0))
        return "\n".join([meta] + [str(c) + " 0" for c in self.cs0])
    
    def __repr__(self):
        return str(self)
            
    def modeled_by(self):
        """Check if the CNF formula is modeled by m"""
        return all(c.modeled_by(self.m) for c in self.cs)


class Clause:

    counter = 0

    def __init__(self, ns):
        """ns - a list of integers representing literals"""
        self.ls = set()
        self.trivial = False
        self.id = Clause.counter
        Clause.counter += 1
        for n in ns:
            l = Literal(n)
            self.ls.add(l)
            # check if both n and -n are present
            if -l in self.ls:
                self.trivial = True
    
    def has_var(self, x):
        l = Literal(x)
        return l in self.ls or -l in self.ls
    
    def xs(self):
        return (l.var for l in self.ls)
    
    def start_watching(self):
        res = list()
        for l in self.ls:
            res.append(l)
            if len(res) == 2:
                break
        assert(len(res) == 2)
        return res
    
    def get_only(self):
        assert(len(self.ls) == 1)
        for l in self.ls:
            return l

    def __contains__(self, l):
        return l in self.ls
    
    def __len__(self):
        return len(self.ls)
    
    def __iter__(self):
        return iter(self.ls)
    
    def __eq__(self, other):
        return self.id == other.id
    
    def __lt__(self, other):
        return self.id < other.id
    
    def __hash__(self):
        return self.id

    def __getitem__(self, x):
        """Return the literal that contains v in this clause"""
        l = Literal(x)
        if l in self.ls:
            return l
        elif -l in self.ls:
            return -l
        else:
            raise IndexError
    
    def modeled_by(self, m):
        """Determine if clause c can be modeled by m"""
        # m can always model clause c if c contains free vars not captured by m
        return any(l not in m or m[l] for l in self.ls)
    
    def modeled_by_modulo(self, m, v):
        """Determine if clause c could be modeled by m if variable v were absent"""
        return any(l not in m or m[l] for l in self.ls if l.var != v)

    def __str__(self):
        return repr(self)
    
    def __repr__(self):
        return repr(self.ls)


class Model:

    def __init__(self):
        self.alpha = dict()
        self.at_level = defaultdict(list)
        self.dv = set()
    
    def has_var(self, x):
        return x in self.alpha
        
    def __contains__(self, l):
        return l.var in self.alpha
    
    def __getitem__(self, l):
        """Return the truth value of literal l under this model"""
        return l.is_neg ^ self.alpha[l.var][0]

    def __len__(self):
        return len(self.alpha)
    
    def commit(self, l, dl, reason):
        """Set literal l to True at level dl according to the given reason clause"""
        x = l.var
        self.alpha[x] = (l.is_pos, dl, reason)
        self.at_level[dl].append(x)
    
    def assign(self, l, dl):
        """Mark v as decision variable, and guess it's True"""
        self.commit(l, dl, None)
        self.dv.add(l.var)
    
    def undo(self, beta):
        """Undo assignments at level > beta"""
        levels = [level for level in self.at_level if level > beta]
        rem_branch = None
        for lvl in levels:
            for x in self.at_level[lvl]:
                if x in self.dv:
                    self.dv.remove(x)
                    if lvl == beta + 1:
                        sign = not self.alpha[x][0]
                        rem_branch = Literal(x) if sign else Literal(-x)
                del(self.alpha[x])
            del(self.at_level[lvl])
        return rem_branch
    
    def __str__(self):
        decision = lambda x: "d" if x in self.dv else ""
        if len(self.alpha) > 0:
            return "\n".join(["-"*5] + ["{} = {} @ {}  {}".format(x, self.alpha[x][0], self.alpha[x][1], decision(x)) \
                for x in sorted(list(self.alpha.keys()))] + ["-"*5])
        else:
            return "(empty model)"
    
    def __repr__(self):
        return str(self)


class Literal:
    
    def __init__(self, n):
        self.n = n
        self.var = abs(n)
        self.is_pos = n > 0
        self.is_neg = n < 0
    
    def __neg__(self):
        return Literal(-self.n)

    def __str__(self):
        return str(self.n)
    
    def __repr__(self):
        return str(self.n)
    
    def __eq__(self, other):
        return self.n == other.n
    
    def __lt__(self, other):
        return self.n < other.n
    
    def __hash__(self):
        return self.n