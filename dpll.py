# cython: language_level=3
# cython: profile=False

from collections import defaultdict
from heapq import heappop, heappush
from random import choice, seed
import logging as logging

LEVEL = logging.INFO
LOG_FILE = 'dpll.log'
logging.basicConfig(level=LEVEL, filename=LOG_FILE, filemode='w', format='%(message)s')

# seed(10)

RESTART_MULTIPLIER = 1

clause_counter = 0

def INFO(dl, msg):
    logging.info(' ' * dl + str(msg))

def DEBUG(dl, msg):
    logging.debug(' ' * dl + str(msg).replace('\n', '\n' + ' ' * dl))

class CDCL:
    def __init__(self, n_vars, nss):
        self.xs = set()
        self.cs0 = list() # includes trivial clauses
        self.cs = list() # non-trivial clauses
        self.watched = dict() # map literal l to clauses that are watching l
        self.pending = list() # literals to be assigned true
        
        # restart using Knuth's reluctant doubling sequence
        self.conflict_count = 0
        self.restart_pair = (1, 1)
        self.reluctant_doubling = lambda u,v: (u+1,1) if (u & -u == v) else (u,2*v)
        
        # Process clauses and variables
        for ns in nss:
            c = Clause(ns)
            self.cs0.append(c)
            if not c.trivial:
                if len(c) == 1:
                    self.pending.append( (0, c.get_only(), c) )
                else:
                    self.cs.append(c)
                    for x in c.xs():
                        self.xs.add(x)

        self.preprocess()
    

    def preprocess(self):
        """Set up watched literals"""
        cs_trivial = list()
        for c in self.cs:
            for l in c.start_watching():
                if l not in self.watched:
                    self.watched[l] = list()
                self.watched[l].append(c)
    

    def run(self):
        """Run CDCL. Return the model if SAT; otherwise return None"""
        
        self.m = Model()

        # decision level 0 is reserved for literals implied during the first
        # unit prop (before making any decision) due to singleton clauses
        self.dl = 0
        if self.unit_prop():
            return None # conflict without decision
        
        self.dl = 1
        while True:
            free = self.free_vars()
            if len(free) == 0:
                break
            l = self.branch(free)
            self.pending.append( (self.dl, l, None) )
            
            conflict = self.unit_prop()

            DEBUG(self.dl, self.m)
            
            if conflict:
                self.conflict_count += 1
            while conflict:
                beta = self.analyze(conflict)
                if beta < 0:
                    return None
                else:
                    l = self.m.undo(beta)
                    INFO(self.dl, "Backtrack to level {}, assert {}".format(beta, l))
                    self.dl = beta
                    if l: # take the other branch
                        self.dl = beta + 1
                        self.pending.append( (self.dl, l, l) )
                        conflict = self.unit_prop()
                    else: # both branches have been taken
                        conflict = True # forced backtrack
                
                DEBUG(self.dl, self.m)

            if self.should_restart():
                self.restart()
            else:
                self.dl += 1
        assert(self.modeled_by())
        return self.m

    
    def watch_correct(self):
        assert(all([c in self.watched[l] for c in self.cs for l in [c[0], c[1]]]))
        assert(all([l in c[:2] for (l, cs) in self.watched.items() for c in cs]))
        
    
    def unit_prop(self):
        """Attempt to apply unit propagation using the current model. Return a conflict, if any"""

        while len(self.pending) > 0: # exit loop when no more literal is pending
            
            dl, l0, reason = self.pending.pop()

            if l0 in self.m:
                if not self.m[l0]:
                    self.pending = list()
                    return reason # conflict
                else:
                    continue # inferred literal is consistent with the model
            
            # update the model
            if reason: # implied
                self.m.commit(l0, dl, reason)
            else: # guessed
                self.m.assign(l0, dl)

            if -l0 not in self.watched:
                continue
            
            watched_new = list() # unit clauses
            for c in self.watched[-l0]:
                
                DEBUG(self.dl, " {} || {}".format(c, c[:2]))
                
                # clause c looks for a substitute literal to watch
                i = 0 if c[0] == -l0 else 1
                j = None
                for i in range(2, len(c)):
                    l = c[i]
                    if l not in self.m or self.m[l]:
                        j = i
                        break

                if j:
                    if c[j] not in self.watched:
                        self.watched[c[j]] = list()
                    self.watched[c[j]].append(c)
                    c[i], c[j] = c[j], c[i]
                    
                    DEBUG(self.dl, c[:2])
                
                # clause c becomes unit, and implies the only remaining watched literal
                else:
                    watched_new.append(c) # c still watches -l0 and the other literal
                    l_other = c[1 - i]
                    self.pending.append( (self.dl, l_other, c) )
                    
                    DEBUG(self.dl, "Unit. Pend {}".format(l_other))
            
            DEBUG(self.dl, "Pending: " + ' '.join([str(t[1]) for t in self.pending]))
            DEBUG(self.dl, self.m)

            self.watched[-l0] = watched_new
        
        return None
    
    def branch(self, free):
        # return Literal(free[0])
        return Literal(choice([-1,1]) * choice(free))

    def free_vars(self):
        """Return the list of free variables (those that are not in model m)"""
        return [x for x in self.xs if not self.m.has_var(x)]
    
    def should_restart(self):
        return self.conflict_count >= self.restart_pair[1] * RESTART_MULTIPLIER
    
    def restart(self):
        INFO(self.dl, "Restart after {} conflicts\n\n\n".format(self.conflict_count))
        self.m.undo(0)
        self.dl = 1
        self.pending = list()
        self.restart_pair = self.reluctant_doubling(*self.restart_pair)
        self.conflict_count = 0
    
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



class Model:

    def __init__(self, ):
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
        if reason:
            INFO(dl, "{}  @  {}  {}".format(l, dl, reason))
    
    def assign(self, l, dl):
        """Mark v as decision variable, and guess it's True"""
        self.commit(l, dl, None)
        self.dv.add(l.var)
        INFO(dl, "{}  @  {}  ----------d----------".format(l, dl))
    
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


class Clause:

    counter = 0

    def __init__(self, ns):
        """ns - a list of integers representing literals"""
        self.ls = list()
        self.trivial = False
        global clause_counter
        self.id = clause_counter
        clause_counter += 1
        ls_set = set()
        for n in ns:
            l = Literal(n)
            self.ls.append(l)
            ls_set.add(l)
            # check if both n and -n are present
            if -l in ls_set:
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
        return self.ls[0]

    # def __contains__(self, l):
        # return l in self.ls
    
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

    def __getitem__(self, i):
        return self.ls[i]
    
    def __setitem__(self, i, l):
        self.ls[i] = l
    
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
        return self.var < other.var and self.is_neg < other.is_neg
    
    def __hash__(self):
        return self.n