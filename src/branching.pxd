# cython: language_level=3
# cython: profile=False

from random import choice
from components cimport Literal, Clause

cdef class ERMA:
    cdef readonly:
        double alpha, alpha_dec, alpha_lb
        int learned_count
        dict q, last_assigned, participated
    
    cdef after_conflict(self, Clause learned, Clause conflict)

    
    cdef on_assign(self, int x)

    
    cdef on_unassign(self, list xs)


    cdef int pick(self, list free)
