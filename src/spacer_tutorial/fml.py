"""Formula manipulation utilities"""

import z3

def free_arith_vars(fml):
    """Returns the set of all integer uninterpreted constants in a formula"""
    seen = set([])
    vars = set([])

    int_sort = z3.IntSort()

    def fv(seen, vars, f):
        if f in seen:
            return
        seen |= {f}
        if f.sort().eq(int_sort) and f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            vars |= {f}
        for ch in f.children():
            fv(seen, vars, ch)

    fv(seen, vars, fml)
    return vars
