# cython: language_level=3
# cython: profile=False

import logging as logging
from collections import defaultdict, deque, Counter
from random import choice, seed, sample
from copy import copy

from components cimport Literal, Clause
from components import Literal, Clause
from branching cimport ERMA
from branching import ERMA

# seed(10)

cdef:
    int RESTART_MULTIPLIER = 1
    int LVL_DEBUG = 0
    int LVL_INFO = 1
    int LVL_WARN = 2

cdef class CDCL:
    cdef readonly:
        int log_level
        list xs, cs0, cs
        set learned
        dict watched
        dict saved_phase
        list assertions
        int conflict_count
        int learning_limit
        tuple restart_counter
        Model m
        bint sat
        int dl
        list ns
        ERMA branching_heuristics
        int n_iter

        
    cdef INFO(self, msg, dl=None):
        if self.log_level > LVL_INFO: return
        if dl is None:
            dl = self.dl
        logging.info('  ' * max(0,dl) + str(msg()))
    
    cdef DEBUG(self, msg, dl=None):
        if self.log_level > LVL_DEBUG: return
        if dl is None:
            dl = self.dl
        logging.debug('  ' * max(0,dl) + str(msg()).replace('\n', '\n' + '  ' * dl))
    

    def __init__(self, n_vars, nss, log_file="log", log_level=LVL_WARN):
        cdef:
            Clause c
            bint sat
            set xs_set
            list stats
            

        logging.basicConfig(level=log_level, filemode='w', filename=log_file, format='%(message)s')
        self.log_level = log_level

        self.xs = list()
        self.cs0 = list() # includes trivial clauses
        self.cs = list() # non-trivial clauses
        self.learned = set()
        self.watched = dict() # map literal l to clauses that are watching l
        self.assertions = list() # literals to be assigned true
        self.conflict_count = 0

        

        # restart using Knuth's reluctant doubleing sequence
        self.restart_counter = (1, 1)
        
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
        
        self.saved_phase = {x: 0 for x in self.xs}
        
        self.learning_limit = max(len(self.cs) // 2, 100)

        self.branching_heuristics = ERMA(self.xs)

        self.n_iter = 0
        self.sat = self.preprocess()

        if self.sat:
            self.sat = self.run()
        
        stats = []
        stats.append("Statistics")
        stats.append("Pre-propcessing iterations: %d" % self.n_iter)
        stats.append("Learned clauses: %d" % len(self.learned))
        self.INFO("\n".join(stats), 0)
    

    cdef bint preprocess(self):
        """Set up watched literals, and infer as much as possible without decision"""
        cdef:
            Clause c
            Literal l
            list cs_trivial = list()
            int fixpoint
            int x
            Literal pos, neg
            
        
        for c in self.cs:
            for l in c.start_watching():
                if l not in self.watched:
                    self.watched[l] = set()
                self.watched[l].add(c)

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
                self.INFO(lambda: "Try {}".format(pos))
                self.assertions.append( (pos, None) )
                conflict = self.unit_prop()
                uv = self.m.undo(-2)
                self.branching_heuristics.on_unassign(uv)
                
                # pos bad ==> assert neg
                if conflict:
                    fixpoint = 2
                    self.INFO(lambda: "pos bad ==> assert neg")
                    self.assertions.append( (neg, Clause([neg]), -2) )
                    # neg also bad
                    conflict = self.unit_prop()
                    if conflict:
                        self.INFO(lambda: "neg also bad")
                        return False
                
                # pos good ==> try neg
                else:
                    self.INFO(lambda: "pos ok ==> try neg")
                    self.assertions.append( (neg, None) )
                    conflict = self.unit_prop()
                    uv = self.m.undo(-2)
                    self.branching_heuristics.on_unassign(uv)

                    # neg bad ==> assert pos
                    if conflict:
                        fixpoint = 2
                        self.INFO(lambda: "neg bad ==> assert pos")
                        self.assertions.append( (pos, Clause([pos]), -2) )
                        assert(not self.unit_prop())
                    # neg good ==> no info
                    else:
                        pass
                        self.INFO(lambda: "neg ok ==> no info")

                # DEBUG(self.dl, str(self.m))
                # DEBUG(self.dl, "")
            fixpoint -= 1
            self.INFO(lambda: "fixpoint={}".format(fixpoint))
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

            # DEBUG(self.dl, self.m)

            while conflict:
                self.conflict_count += 1
                beta, only_true, learned = self.analyze(conflict)
                if beta < 0:
                    return None
                else:
                    self.INFO(lambda: "Backtrack to level {}".format(beta))
                    if not learned.singleton:
                        self.learned.add(learned)
                    self.branching_heuristics.after_conflict(learned, conflict)
                    # assert(self.m[only_true])
                    uv = self.m.undo(beta)
                    self.branching_heuristics.on_unassign(uv)
                    self.dl = beta
                    self.INFO(lambda: "Assert {}".format(only_true))
                    self.assertions.append( (only_true, learned) )
                    conflict = self.unit_prop()

                # DEBUG(self.dl, self.m)

            if self.should_restart():
                self.restart()
            else:
                self.dl += 1
        
        assert(self.modeled_by()) # make sure that, if sat, the model is indeed correct
        
        return self.m

    
    def watch_correct(self):
        assert(all([c in self.watched[l] for c in self.cs for l in [c[0], c[1]]]))
        assert(all([l in c[:2] for (l, cs) in self.watched.items() for c in cs]))
        
    
    cdef unit_prop(self):
        """Attempt to apply unit propagation using the current model. Return a conflict, if any"""
        cdef:
            Literal l, l_other, lk
            Clause reason
            tuple t
            int dl
            set watched_new
            int i, j, k
            

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
                self.INFO(lambda: "{:>3}  @  {}  {}".format(str(l), self.dl, reason))
            else: # guessed
                self.m.assign(l, dl)
                self.INFO(lambda: "{:>3}  @  {}  ----------d----------".format(str(l), self.dl))
            
            self.saved_phase[l.var] = l.sign()
            self.branching_heuristics.on_assign(l.var)

            if -l not in self.watched:
                continue # nothing is watching -l
            
            watched_new = set() # unit clauses
            for c in self.watched[-l]:
                
                # clause c looks for a substitute literal to watch
                i = 0 if c[0] == -l else 1
                j = -1
                for k in range(2, len(c)):
                    lk = c[k]
                    if lk not in self.m or self.m[lk]:
                        j = k
                        break

                if j >= 0:
                    if c[j] not in self.watched:
                        self.watched[c[j]] = set()
                    self.watched[c[j]].add(c)
                    c[i], c[j] = c[j], c[i]
                    
                
                # clause c becomes unit, and implies the only remaining watched literal
                else:
                    watched_new.add(c) # c still watches -l and the other literal
                    l_other = c[1 - i]
                    self.assertions.append( (l_other, c) )

            self.watched[-l] = watched_new
        
        return None
    
    
    cdef Literal branch(self, list free):
        """Choose a random free variable and a polarity to branch on"""
        cdef:
            int x
            int sign
        x = self.branching_heuristics.pick(free)
        sign = self.saved_phase[x]
        if sign == 0: # no previously saved phase
            sign = choice([-1,1])
        return Literal(sign * x)


    cdef list free_vars(self):
        """Return the list of free variables (those that are not in model m)"""
        return [x for x in self.xs if not self.m.has_var(x)]
    

    cdef bint should_restart(self):
        """Check if we should restart search"""
        return self.conflict_count >= self.restart_counter[1] * RESTART_MULTIPLIER
    
    cdef reluctant_doubling(self):
        u, v = self.restart_counter
        self.restart_counter = (u+1,1) if (u & -u == v) else (u,2*v)
    

    cdef restart(self):
        """Restart search"""
        self.INFO(lambda: "Restart after {} conflicts\n\n\n".format(self.conflict_count), 0)
        self.INFO(lambda: self.m, 0)
        uv = self.m.undo(0)
        self.branching_heuristics.on_unassign(uv)
        self.dl = 1
        self.assertions = list()
        self.reluctant_doubling()
        self.conflict_count = 0
        if len(self.learned) > self.learning_limit:
            self.forget()

    cdef forget(self):
        cdef:
            int num_keep, num_forget
            list to_forget
            Clause c
            int i
            Literal l

        num_keep = self.learning_limit // 2
        num_forget = len(self.learned) - num_keep
        to_forget = sample(self.learned, k=num_forget)
        self.INFO(lambda: "Learned {} out of {} allowed, keep {}".format(len(self.learned), self.learning_limit, num_keep))
        for c in to_forget:
            for i in range(2):
                l = c[i]
                self.watched[l].remove(c)
            self.learned.remove(c)


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
        self.INFO(lambda: "Learned {}".format(clause_str(learned)))
        only_true = next(filter(lambda l: self.m.level_of(l) == self.dl, learned))
        return learned, only_true
        
        
    def uip(self, conflict):

        frontier, old_frontier = conflict, None
        at_curr_level = lambda l: self.m.level_of(l) == self.dl
        clause_str = lambda c: "[" + ",  ".join(["{}  @{}".format(l, self.m.level_of(l)) for l in c]) + "]"
        self.INFO(lambda: "Conflict frontier {}".format(clause_str(frontier)))
        
        while True:

            for l in list(frontier):
                assert(l in self.m)
                reason = self.m.predecessor(l)
                if reason: # not a decision literal
                    assert(-l in reason)
                    if reason.singleton:
                        pass
                        self.INFO(lambda: "Trace {} to singleton {}".format(-l, clause_str(reason)))
                    else:
                        self.INFO(lambda: "Trace {} to {}".format(-l, clause_str(reason)))
                        frontier = frontier.resolve(reason, l.var)
                        self.INFO(lambda: "Resolvent {}".format(clause_str(frontier)))

            ls_curr = [l for l in frontier if at_curr_level(l)]
            if old_frontier and old_frontier.equiv(frontier) or len(ls_curr) == 1:
                break
            old_frontier = frontier
                    
            # if not actual.equiv(expected):
            #     self.INFO(lambda: "expected = {}, actual = {}".format(expected, actual))
            #     assert(False)
        

        assert(len(ls_curr) == 1)
        learned = Clause(frontier)
        only_true = ls_curr[0]
        self.INFO(lambda: "Learned {}".format(clause_str(learned)))
        return learned, only_true
    

    def analyze(self, Clause conflict):
        """Analyze the conflict and return the level to which to backtrack"""
        cdef:
            Clause learned
            Literal only_true
        learned, only_true = self.uip_fast(conflict)
        i = learned.index(only_true)
        
        if learned.singleton:
            beta = self.dl - 1
        else:
            # only one literal is true after backjump
            # put that literal at index 0
            learned[0], learned[i] = learned[i], learned[0]
            # set up watch list for the newly learned clause
            for i in range(2):
                l = learned[i]
                if l not in self.watched:
                    self.watched[l] = set()
                self.watched[l].add(learned)
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


cdef class Model:
    cdef readonly:
        dict alpha, at_level
        set dv

    def __init__(self):
        self.alpha = dict()
        self.at_level = dict()
        self.dv = set()
    
    def has_var(self, x):
        return x in self.alpha
        
    def __contains__(self, Literal l):
        return l.var in self.alpha
    
    def __getitem__(self, Literal l):
        """Return the truth value of literal l under this model"""
        return l.is_neg ^ self.alpha[l.var][0]

    def __len__(self):
        return len(self.alpha)
    

    cdef Clause predecessor(self, Literal l):
        _, _, reason = self.alpha[l.var]
        return reason
    

    cdef int level_of(self, Literal l):
        _, dl, _ = self.alpha[l.var]
        return dl


    cdef commit(self, Literal l, dl, reason):
        """Set literal l to True at level dl according to the given reason clause"""
        x = l.var
        assert(x != 0)
        self.alpha[x] = (l.is_pos, dl, reason)
        if dl not in self.at_level:
            self.at_level[dl] = list()
        self.at_level[dl].append(x)
        if reason:
            assert(l in reason)
    

    cdef assign(self, Literal l, dl):
        """Mark v as decision variable, and guess it's True"""
        self.commit(l, dl, None)
        self.dv.add(l.var)
        
    
    cdef list undo(self, int beta):
        """Undo assignments at level > beta"""
        cdef:
            list unassigned, levels
            int lvl, x

        unassigned = list()
        levels = [level for level in self.at_level if level > beta]
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
