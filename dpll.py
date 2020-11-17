#cython: language_level=3

class CNF:
    def __init__(self, n_vars, cs0):
        self.vs = set(range(1, n_vars+1))
        self.cs0 = cs0 # includes trivial clauses
        self.cs = set(c for c in cs0 if not c.trivial) # excludes trivial clauses
        self.contains = {v: set([c for c in self.cs if v in c]) for v in self.vs} # clauses that contain v

    def __str__(self):
        meta = "p cnf {} {}".format(len(self.vs), len(self.cs0))
        return "\n".join([meta] + [str(c) + ' 0' for c in self.cs0])
    
    def free_vars(self, m):
        return [v for v in self.vs if v not in m]
    
    def modeled_by(self, m):
        return all((c.modeled_by(m) for c in self.cs))
    
    def unit_prop(self, m, l, c):
        m.commit(l) # declare literal l is true in model m
        c.trivial = True
        self.cs.remove(c)
    
    def dpll(self):
        m = Model()
        while True:
            free = self.free_vars(m)
            if len(free) > 0:
                # greedily search for unit-propagation variables
                up = list()
                for v in free:
                    for c in self.contains[v]:
                        if not c.modeled_by_modulo(m, v):
                            up.append((v, c))
                            break
                if len(up) == 0:
                    m.guess(free[0]) # mark the first free var as decision var
                else:
                    for v, c in up:
                        self.unit_prop(m, c[v], c)
            # no more free variables 
            else:
                while True:
                    # all clauses are modeled by m ==> SAT
                    if all(map(lambda c: c.modeled_by(m), self.cs)):
                        return True
                    # some clause is not modeled
                    # no more decision variables left ==> UNSAT
                    if len(m.dv) == 0:
                        return False
                    m.backtrack() # backtrack the last decision variable


class Literal:
    def __init__(self, n):
        assert(n != 0)
        self.n = n
    
    def var(self):
        return abs(self.n)
    
    def is_pos(self):
        return self.n > 0
    
    def is_neg(self):
        return self.n < 0

    def __str__(self):
        return str(self.n)
    
    def __eq__(self, other):
        return self.n == other.n
    
    def __hash__(self):
        return hash(self.n)


class Clause:
    def __init__(self, ns):
        """Initialize a clause from a list of integers representing literals"""
        self.ls = set() # literals
        self.trivial = False
        for n in ns:
            # check if both n and -n are present
            if Literal(-n) in self.ls:
                self.trivial = True
            self.ls.add(Literal(n))

    def __str__(self):
        return ' '.join([str(l) for l in self.ls])
    
    def __contains__(self, l):
        if type(l) == Literal:
            return l in self.ls
        else: # otherwise, l is a variable
            return Literal(l) in self.ls or Literal(-l) in self.ls
    
    def __getitem__(self, v):
        """Return the literal that contains v in this clause"""
        pos, neg = Literal(v), Literal(-v)
        if pos in self.ls:
            return pos
        elif neg in self.ls:
            return neg
        else:
            raise IndexError
    
    def modeled_by(self, m):
        """Determine if clause c can be modeled by m"""
        # m can always model clause c if c contains free vars not captured by m
        return any((l not in m or m[l] for l in self.ls))
    
    def modeled_by_modulo(self, m, v):
        """Determine if clause c could be modeled by m if variable v were absent"""
        return any((l not in m or m[l] for l in self.ls if l.var() != v))


class Model:
    def __init__(self):
        self.dv = list() # decision variables
        self.alpha = dict() # assignment function
    
    def __contains__(self, l):
        if type(l) == Literal:
            return l.var() in self.alpha
        else: # otherwise, l is a variable
            return l in self.alpha
    
    def __getitem__(self, l):
        """Return the truth value of literal l under this model"""
        return l.is_neg() ^ self.alpha[l.var()]
    
    def commit(self, l):
        """Set literal l to true"""
        self.alpha[l.var()] = l.is_pos()
    
    def guess(self, v):
        self.alpha[v] = True # guess True first
        self.dv.append(v)
    
    def backtrack(self):
        v = self.dv.pop() # v becomes decided
        self.alpha[v] = not self.alpha[v] # guess the remaining option
        return v
    
    def __str__(self):
        postfix = lambda v: "_d" if v in self.dv else ""
        if len(self.alpha) > 0:
            return ", ".join(["{}{}: {}".format(v, postfix(v), self.alpha[v]) \
                for v in self.alpha])
        else:
            return "(empty model)"