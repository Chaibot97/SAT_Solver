# cython: language_level=3
# cython: profile=False

cdef class Clause:
    cdef readonly:
        int id
        list ls
        bint singleton
        bint trivial

    cdef bint has_var(self, int x)
    
    cdef list xs(self)
    
    cdef list start_watching(self)
    
    cdef Literal get_only(self)

    cdef int index(self, Literal l)


cdef class Literal:
    cdef:
        readonly int var # positive integer representing the variable name
        bint is_pos
        bint is_neg
        int n # +var or -var
    
    cdef int sign(self)