# cython: language_level=3
# cython: profile=False

class CNF:
    def __init__(self, n_vars, nss):
        self.vs = set(range(1, n_vars+1))
        self.cs0 = [Clause(ns) for ns in nss] # includes trivial clauses
        self.cs = set(c for c in self.cs0 if not c.trivial) # excludes trivial clauses
        self.contains = {v: set(c for c in self.cs if c.has_var(v)) for v in self.vs} # non-trivial clauses that contain v

    def __str__(self):
        meta = "p cnf {} {}".format(len(self.vs), len(self.cs0))
        return "\n".join([meta] + [str(c) + " 0" for c in self.cs0])
    
    def free_vars(self, m):
        """Return the list of free variables (those that are not in model m)"""
        return [v for v in self.vs if not m.has_var(v)]
    
    def modeled_by(self, m):
        """Check if the CNF formula is modeled by m"""
        return all(c.modeled_by(m) for c in self.cs)
    
    def unit_prop(self, m, v, c):
        """Do unit-propagation on literal l in clause c"""
        l = c[v]
        m.commit(l) # declare literal l to be true in model m
        ts = list() # trivial clauses that result from unit prog
        for c in self.contains[v]:
            if not c.trivial:
                if l in c:
                    ts.append(c)
        for c in ts:
            c.trivial = True
            self.cs.remove(c)
    
    def dpll(self):
        m = Model()

        while True:
            free = self.free_vars(m)
            sat = self.modeled_by(m)
            
            # check if we're done
            if len(free) == 0:
                if sat:
                    return True
                if len(m.dv) == 0 and not sat:
                    return False
            
            # if not done, we either need to backtrack, or can branch on a free variable
            if len(m.dv) > 0 and not sat:
                m.backtrack()
            # otherwise, there has to be a free var (by logic)
            else:
                up = list() # unit-prop var
                for v in free:
                    for c in self.contains[v]:
                        if not c.trivial and not c.modeled_by_modulo(m, v):
                            up.append((v, c))
                            break
                
                if len(up) == 0:
                    m.guess(free[0]) # mark the first free var as decision var
                else:
                    for v, c in up:
                        self.unit_prop(m, v, c)


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
    
    def __eq__(self, other):
        return self.n == other.n
    
    def __hash__(self):
        return self.n


class Clause:

    def __init__(self, ns):
        """ns - a list of integers representing literals"""
        self.ls = set() # literals
        self.trivial = False
        for n in ns:
            l = Literal(n)
            self.ls.add(l)
            # check if both n and -n are present
            if -l in self.ls:
                self.trivial = True
    
    def has_var(self, v):
        l = Literal(v)
        return l in self.ls or -l in self.ls
    
    def __contains__(self, l):
        return l in self.ls
    
    def __getitem__(self, v):
        """Return the literal that contains v in this clause"""
        l = Literal(v)
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
        return " ".join([str(l) for l in self.ls])


class Model:

    def __init__(self):
        self.dv = list()
        self.alpha = dict()
    
    def has_var(self, v):
        return v in self.alpha
        
    def __contains__(self, l):
        return l.var in self.alpha
    
    def __getitem__(self, l):
        """Return the truth value of literal l under this model"""
        return l.is_neg ^ self.alpha[l.var]
    
    def commit(self, l):
        """Set literal l to true"""
        self.alpha[l.var] = l.is_pos
    
    def guess(self, v):
        """Mark v as decison variable, and guess it's True"""
        self.alpha[v] = True
        self.dv.append(v)
    
    def backtrack(self):
        """Backtrack the latest decision variable and take the other branch"""
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