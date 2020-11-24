# cython: language_level=3
# cython: profile=False

from random import choice
from components cimport Literal, Clause

cdef class ERMA:

    def __init__(self, xs, alpha=0.4, alpha_dec=10**(-6), alpha_lb=0.06):
        self.alpha = alpha
        self.alpha_dec = alpha_dec
        self.alpha_lb = alpha_lb
        self.learned_count = 0
        self.q = {x: 0 for x in xs}
        self.last_assigned = {x: 0 for x in xs}
        self.participated = {x: 0 for x in xs}

    
    cdef after_conflict(self, Clause learned, Clause conflict):
        self.learned_count += 1
        for x in set(learned.xs()) | set(conflict.xs()):
            self.participated[x] += 1
        if self.alpha > self.alpha_lb:
            self.alpha -= self.alpha_dec
    
    cdef on_assign(self, int x):
        self.last_assigned[x] = self.learned_count
        self.participated[x] = 0
    
    cdef on_unassign(self, list xs):
        cdef int x
        for x in xs:
            interval = self.learned_count - self.last_assigned[x]
            if interval > 0:
                r = self.participated[x] / interval
                self.q[x] = (1 - self.alpha) * self.q[x] + self.alpha * r

    cdef int pick(self, list free):
        q, x = max([(self.q[x], x) for x in free], key=lambda p:p[0])
        return x