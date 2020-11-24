# cython: language_level=3
# cython: profile=False

clause_counter = 0

cdef class Clause:

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
        cdef:
            Clause c
            set ls
            bint trivial
            Literal l

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
    
    def resolve(self, Clause other, int on):
        cdef:
            set ls = set()
            Literal l
        for l in self.ls:
            if l.var != on:
                ls.add(l)
        for l in other.ls:
            if l.var != on:
                ls.add(l)
        return Clause(ls)
    
    def equiv(self, other):
        return len(self) == len(other) and all([l in other for l in self])
    
    
    cdef bint has_var(self, int x):
        cdef Literal l = Literal(x)
        return l in self.ls or -l in self.ls
    
    cdef list xs(self):
        cdef Literal l
        return [l.var for l in self.ls]
    
    cdef list start_watching(self):
        cdef:
            list res = list()
            Literal l
        for l in self.ls:
            res.append(l)
            if len(res) == 2:
                break
        assert(len(res) == 2)
        return res
    
    cdef Literal get_only(self):
        assert(len(self.ls) == 1)
        return self.ls[0]

    cdef int index(self, Literal l):
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


cdef class Literal:
    
    def __init__(self, n):
        self.n = n
        self.var = abs(n)
        self.is_pos = n > 0
        self.is_neg = n < 0
    
    cdef int sign(self):
        return 1 if self.is_pos else -1
    
    def __neg__(self):
        return Literal(-self.n)

    def __str__(self):
        return str(self.n)
    
    def __repr__(self):
        return str(self.n)
    
    def __eq__(self, Literal other):
        return self.n == other.n
    
    def __lt__(self, Literal other):
        return self.var < other.var and self.is_neg < other.is_neg
    
    def __hash__(self):
        return self.n

