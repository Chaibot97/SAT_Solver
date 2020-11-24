# cython: language_level=3
# cython: profile=False

import logging as logging
from collections import defaultdict, deque, Counter
from random import choice, seed
from branching import ERMA

LEVEL = logging.INFO

seed(10)

RESTART_MULTIPLIER = 1

clause_counter = 0

def INFO(dl, msg):
    logging.info('  ' * max(0,dl) + str(msg))

def DEBUG(dl, msg):
    logging.debug('  ' * max(0,dl) + str(msg).replace('\n', '\n' + '  ' * dl))


class CDCL:
    def __init__(self, n_vars, nss, log_file="log"):
        logging.basicConfig(level=LEVEL, filemode='w', filename=log_file, format='%(message)s')
        self.xs = list()
        self.cs0 = list() # includes trivial clauses
        self.cs = list() # non-trivial clauses
        self.watched = dict() # map literal l to clauses that are watching l
        self.assertions = list() # literals to be assigned true
        self.conflict_count = 0
        self.learned_clause = 0

        # restart using Knuth's reluctant doubleing sequence
        self.restart_counter = (1, 1)
        self.reluctant_doubling = lambda u,v: (u+1,1) if (u & -u == v) else (u,2*v)
        
        # decision levels:
        #   -2 :: assertions of singleton clauses and implied literals in pre-processing stage
        #   -1 :: decision level for pre-processing stage
        #  > 0 :: normal decisions
        self.m = Model()
        self.sat = False
        self.dl = -2
        
        xs_set = set()
        # process clauses and variables
        for ns in nss:
            c = Clause.from_ns(ns)
            self.cs0.append(c)
            if not c.trivial:
                if c.singleton: # singleton clause
                    self.assertions.append( (c.get_only(), c) )
                else:
                    self.cs.append(c)
                    for x in c.xs():
                        if x not in xs_set:
                            xs_set.add(x)
                            self.xs.append(x)
        
        self.branching_heuristics = ERMA(self.xs)

        self.n_iter = 0
        self.sat = self.preprocess()

        if self.sat:
            self.sat = self.run()
        
        stats = []
        stats.append("Statistics")
        stats.append("Pre-propcessing iterations: %d" % self.n_iter)
        stats.append("Learned clauses: %d" % self.learned_clause)
        INFO(0, "\n".join(stats))
    

    def preprocess(self):
        """Set up watched literals, and infer as much as possible without decision"""
        cs_trivial = list()
        for c in self.cs:
            for l in c.start_watching():
                if l not in self.watched:
                    self.watched[l] = list()
                self.watched[l].append(c)

        if self.unit_prop():
            return False
        
        # try both polarities of each variable
        self.dl = -1
        fixpoint = 2 # needs 2 iterations to detect fixpoint
        while fixpoint > 0:
            # if self.n_iter > 10:
                # break
            for x in self.xs:
                if x in self.m.alpha:
                    continue
                pos, neg = Literal(x), Literal(-x)
                
                # try pos
                INFO(self.dl, "Try {}".format(pos))
                self.assertions.append( (pos, None) )
                conflict = self.unit_prop()
                uv = self.m.undo(-2)
                self.branching_heuristics.on_unassign(uv)
                
                # pos bad ==> assert neg
                if conflict:
                    fixpoint = 2
                    INFO(self.dl, "pos bad ==> assert neg")
                    self.assertions.append( (neg, Clause([neg]), -2) )
                    # neg also bad
                    conflict = self.unit_prop()
                    if conflict:
                        INFO(self.dl, "neg also bad")
                        return False
                
                # pos good ==> try neg
                else:
                    INFO(self.dl, "pos ok ==> try neg")
                    self.assertions.append( (neg, None) )
                    conflict = self.unit_prop()
                    uv = self.m.undo(-2)
                    self.branching_heuristics.on_unassign(uv)

                    # neg bad ==> assert pos
                    if conflict:
                        fixpoint = 2
                        INFO(self.dl, "neg bad ==> assert pos")
                        self.assertions.append( (pos, Clause([pos]), -2) )
                        assert(not self.unit_prop())
                    # neg good ==> no info
                    else:
                        INFO(self.dl, "neg ok ==> no info")

                DEBUG(self.dl, str(self.m))
                DEBUG(self.dl, "")
            fixpoint -= 1
            INFO(self.dl, "fixpoint={}".format(fixpoint))
            self.n_iter += 1
        return True


    def run(self):
        """Run CDCL. Return the model if SAT, or None otherwise"""
        
        self.dl = 1
        while True:
            free = self.free_vars()
            if len(free) == 0:
                break
            l = self.branch(free)
            self.assertions.append( (l, None) )
            
            conflict = self.unit_prop()

            DEBUG(self.dl, self.m)

            while conflict:
                self.conflict_count += 1
                beta, only_true, learned = self.analyze(conflict)
                if beta < 0:
                    return None
                else:
                    INFO(self.dl, "Backtrack to level {}".format(beta))
                    self.cs.append(learned)
                    self.learned_clause += 1
                    # assert(self.m[only_true])
                    uv = self.m.undo(beta)
                    self.branching_heuristics.on_unassign(uv)
                    self.dl = beta
                    INFO(self.dl, "Assert {}".format(only_true))
                    self.assertions.append( (only_true, learned) )
                    conflict = self.unit_prop()

                DEBUG(self.dl, self.m)

            if self.should_restart():
                self.restart()
            else:
                self.dl += 1
        
        assert(self.modeled_by()) # make sure that, if sat, the model is indeed correct
        
        return self.m

    
    def watch_correct(self):
        assert(all([c in self.watched[l] for c in self.cs for l in [c[0], c[1]]]))
        assert(all([l in c[:2] for (l, cs) in self.watched.items() for c in cs]))
        
    
    def unit_prop(self):
        """Attempt to apply unit propagation using the current model. Return a conflict, if any"""

        while len(self.assertions) > 0: # exit loop when no more literal is pending
            
            t = self.assertions.pop()

            if len(t) == 2:
                l, reason = t
                dl = self.dl
            elif len(t) == 3:
                l, reason, dl = t

            if l in self.m:
                if not self.m[l]:
                    self.assertions = list()
                    return reason # conflict
                else:
                    continue # inferred literal is consistent with the model
            
            # update the model
            if reason: # implied
                self.m.commit(l, dl, reason)
                INFO(self.dl, "{:>3}  @  {}  {}".format(str(l), self.dl, reason))
            else: # guessed
                self.m.assign(l, dl)
                INFO(self.dl, "{:>3}  @  {}  ----------d----------".format(str(l), self.dl))
            
            self.branching_heuristics.on_assign(l.var)

            if -l not in self.watched:
                continue # nothing is watching -l
            
            watched_new = list() # unit clauses
            for c in self.watched[-l]:
                
                DEBUG(self.dl, " {} || {}".format(c, c[:2]))
                
                # clause c looks for a substitute literal to watch
                i = 0 if c[0] == -l else 1
                j = None
                for k in range(2, len(c)):
                    lk = c[k]
                    if lk not in self.m or self.m[lk]:
                        j = k
                        break

                if j:
                    if c[j] not in self.watched:
                        self.watched[c[j]] = list()
                    self.watched[c[j]].append(c)
                    c[i], c[j] = c[j], c[i]
                    
                    DEBUG(self.dl, c[:2])
                
                # clause c becomes unit, and implies the only remaining watched literal
                else:
                    watched_new.append(c) # c still watches -l and the other literal
                    l_other = c[1 - i]
                    self.assertions.append( (l_other, c) )
                    
                    DEBUG(self.dl, "Unit. Pend {}".format(l_other))
            
            DEBUG(self.dl, "Pending: " + ' '.join([str(t[1]) for t in self.assertions]))
            DEBUG(self.dl, self.m)

            self.watched[-l] = watched_new
        
        return None
    
    
    def branch(self, free):
        """Choose a random free variable and a polarity to branch on"""
        # x = self.branching_heuristics.pick(free)
        x = choice(free)
        # return Literal(free[0])
        return Literal(choice([-1,1]) * x)


    def free_vars(self):
        """Return the list of free variables (those that are not in model m)"""
        return [x for x in self.xs if not self.m.has_var(x)]
    

    def should_restart(self):
        """Check if we should restart search"""
        return self.conflict_count >= self.restart_counter[1] * RESTART_MULTIPLIER
    

    def restart(self):
        """Restart search"""
        INFO(0, "Restart after {} conflicts\n\n\n".format(self.conflict_count))
        INFO(0, self.m)
        uv = self.m.undo(0)
        self.branching_heuristics.on_unassign(uv)
        self.dl = 1
        self.assertions = list()
        self.restart_counter = self.reluctant_doubling(*self.restart_counter)
        self.conflict_count = 0


    def uip_fast(self, conflict):
        clause_str = lambda c: "[" + ",  ".join(["{}  @{}".format(l, self.m.level_of(l)) for l in c]) + "]"
        frontier = deque(conflict)
        frontier_set = set(frontier)
        level_count = Counter()
        for l in frontier:
            level_count[self.m.level_of(l)] += 1

        end = None
        frontier.append(end)
        changes = 0 # change since last seen end
        while True:
            if level_count[self.dl] == 1: break
            l = frontier.popleft()
            if l is end and changes == 0:
                break
            
            if l is end:
                changes = 0 # reset
                frontier.append(end)
            else:
                reason = self.m.predecessor(l)
                if not reason: # decision variable
                    frontier.append(l)
                else:
                    level_count[self.m.level_of(l)] -= 1
                    for m in reason:
                        if m != -l and m not in frontier_set:
                            frontier.append(m)
                            frontier_set.add(m)
                            changes += 1
                            level_count[self.m.level_of(m)] += 1
        
        assert(level_count[self.dl] == 1)
        learned = Clause([l for l in frontier if l is not end])
        INFO(self.dl, "Learned {}".format(clause_str(learned)))
        only_true = next(filter(lambda l: self.m.level_of(l) == self.dl, learned))
        return learned, only_true
        
        
    def uip(self, conflict):

        frontier, old_frontier = conflict, None
        at_curr_level = lambda l: self.m.level_of(l) == self.dl
        clause_str = lambda c: "[" + ",  ".join(["{}  @{}".format(l, self.m.level_of(l)) for l in c]) + "]"
        INFO(self.dl, "Conflict frontier {}".format(clause_str(frontier)))
        
        while True:

            for l in list(frontier):
                assert(l in self.m)
                reason = self.m.predecessor(l)
                if reason: # not a decision literal
                    assert(-l in reason)
                    if reason.singleton:
                        INFO(self.dl, "Trace {} to singleton {}".format(-l, clause_str(reason)))
                    else:
                        INFO(self.dl, "Trace {} to {}".format(-l, clause_str(reason)))
                        frontier = frontier.resolve(reason, l.var)
                        INFO(self.dl, "Resolvent {}".format(clause_str(frontier)))

            ls_curr = [l for l in frontier if at_curr_level(l)]
            if old_frontier and old_frontier.equiv(frontier) or len(ls_curr) == 1:
                break
            old_frontier = frontier
                    
            # if not actual.equiv(expected):
            #     INFO(self.dl, "expected = {}, actual = {}".format(expected, actual))
            #     assert(False)
        

        assert(len(ls_curr) == 1)
        learned = Clause(frontier)
        only_true = ls_curr[0]
        INFO(self.dl, "Learned {}".format(clause_str(learned)))
        return learned, only_true
    

    def analyze(self, conflict):
        """Analyze the conflict and return the level to which to backtrack"""
    
        # learned, only_true = self.uip(conflict)
        learned, only_true = self.uip_fast(conflict)
        i = learned.index(only_true)
        
        if learned.singleton:
            beta = self.dl - 1
        else:
            self.cs.append(learned)
            # only one literal is true after backjump
            # put that literal at index 0
            learned[0], learned[i] = learned[i], learned[0]
            # set up watch list for the newly learned clause
            for i in range(2):
                l = learned[i]
                if l not in self.watched:
                    self.watched[l] = list()
                self.watched[l].append(learned)
            beta = max(0, max([self.m.level_of(l) for l in learned if l != only_true]))
        return beta, only_true, learned


    def modeled_by(self):
        """Check if the CNF formula is modeled by m"""
        return all(c.modeled_by(self.m) for c in self.cs)


    def __str__(self):
        meta = "p cnf {} {}".format(len(self.vs), len(self.cs0))
        return "\n".join([meta] + [str(c) + " 0" for c in self.cs0])
    

    def __repr__(self):
        return str(self)


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
    

    def predecessor(self, l):
        _, _, reason = self.alpha[l.var]
        return reason
    

    def level_of(self, l):
        _, dl, _ = self.alpha[l.var]
        return dl


    def commit(self, l, dl, reason):
        """Set literal l to True at level dl according to the given reason clause"""
        x = l.var
        assert(x != 0)
        self.alpha[x] = (l.is_pos, dl, reason)
        self.at_level[dl].append(x)
        if reason:
            assert(l in reason)
    

    def assign(self, l, dl):
        """Mark v as decision variable, and guess it's True"""
        self.commit(l, dl, None)
        self.dv.add(l.var)
        
    
    def undo(self, beta):
        """Undo assignments at level > beta"""
        levels = [level for level in self.at_level if level > beta]
        unassigned = list()
        for lvl in levels:
            for x in self.at_level[lvl]:
                if x in self.dv:
                    self.dv.remove(x)
                del(self.alpha[x])
                unassigned.append(x)
            del(self.at_level[lvl])
        return unassigned
    
    def __str__(self):
        is_dv = lambda x: "d" if x in self.dv else ""
        to_lit = lambda x: (1 if self.alpha[x][0] else -1) * x
        sep = ["-"*5 + "(model)" + "-"*5]
        if len(self.alpha) > 0:
            return "\n".join(sep + ["{:>3}  @  {:>2}  {}".format(to_lit(x), self.alpha[x][1], is_dv(x)) \
                for x in sorted(list(self.alpha.keys()))] + sep)
        else:
            return "(empty model)"
    
    def __repr__(self):
        return str(self)


class Clause:

    counter = 0

    def __init__(self, ls):
        global clause_counter
        self.id = clause_counter
        clause_counter += 1

        self.ls = [l for l in ls]
        self.singleton = len(self.ls) == 1
        # assume non-triviality
        self.trivial = False

    @classmethod
    def from_ns(cls, ns):
        """ns - a list of integers representing literals"""

        ls = set()
        trivial = False
        for n in ns:
            l = Literal(n)
            ls.add(l)
            # check if both n and -n are present
            if -l in ls:
                trivial = True

        c = cls(ls)
        c.trivial = trivial
        return c
    
    def resolve(self, other, on):
        ls = set()
        for l in self.ls:
            if l.var != on:
                ls.add(l)
        for l in other.ls:
            if l.var != on:
                ls.add(l)
        return Clause(ls)
    
    def equiv(self, other):
        return len(self) == len(other) and all([l in other for l in self])
    
    
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

    def index(self, l):
        return self.ls.index(l)
    
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