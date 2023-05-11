"""Formula manipulation utilities"""

import z3

def free_arith_vars(fml):
    """Returns the set of all integer uninterpreted constants in a formula"""
    seen = set([])
    vars = set([])

    int_sort = z3.IntSort()
    real_sort = z3.RealSort()

    sorts = [int_sort, real_sort]

    def fv(seen, vars, f):
        if f in seen:
            return
        seen |= {f}
        if (f.sort() in sorts) and f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            vars |= {f}
        for ch in f.children():
            fv(seen, vars, ch)

    fv(seen, vars, fml)
    return vars

def mk_lt(lhs, rhs):
    if z3.is_int_value(rhs):
        return mk_le(lhs, z3.simplify(rhs - 1))
    elif z3.is_int_value(lhs):
        return mk_gt(rhs, lhs)
    return lhs < rhs
def mk_le(lhs, rhs):
    if z3.is_int_value(rhs) and rhs.as_long() == 0 and z3.is_add(lhs):
        L, R = [], []
        for k in lhs.children():
            if z3.is_mul(k) and z3.is_int_value(k.arg(0)) and k.arg(0).as_long() == -1:
                R.append(k.arg(1))
            else:
                L.append(k)
        if len(L) > 0 and len(R) > 0:
            return z3.Sum(L) <= z3.Sum(R)
    return lhs <= rhs
def mk_gt(lhs, rhs):
    if z3.is_int_value(rhs):
        return mk_ge(lhs, z3.simplify(rhs + 1))
    elif z3.is_int_value(lhs):
        return mk_lt(rhs, lhs)
    return lhs > rhs
def mk_ge(lhs, rhs):
    if z3.is_int_value(rhs) and rhs.as_long() == 0 and z3.is_add(lhs):
        L, R = [], []
        for k in lhs.children():
            if z3.is_mul(k) and z3.is_int_value(k.arg(0)) and k.arg(0).as_long() == -1:
                R.append(k.arg(1))
            else:
                L.append(k)
        if len(L) > 0 and len(R) > 0:
            return z3.Sum(L) >= z3.Sum(R)

    return lhs >= rhs

def mk_not(exp):
    if z3.is_not(exp): return exp
    if z3.is_lt(exp): return mk_ge(exp.arg(0), exp.arg(1))
    if z3.is_le(exp): return mk_gt(exp.arg(0), exp.arg(1))
    if z3.is_gt(exp): return mk_le(exp.arg(0), exp.arg(1))
    if z3.is_ge(exp): return mk_lt(exp.arg(0), exp.arg(1))
    if z3.is_implies(exp): 
        return z3.And(exp.arg(0), mk_not(exp.arg(1)))

    return z3.Not(exp)

def mk_or(k):
    if (len(k) == 2):
        return z3.Implies(mk_not(k[0]), k[1])

    return z3.Or(k)
def push_not(exp):
    if z3.is_not(exp):
        return mk_not(exp.arg(0))
    elif z3.is_and(exp):
        kids = [push_not(k) for k in exp.children()]
        return z3.And(*kids) 
    elif z3.is_or(exp):
        kids = [push_not(k) for k in exp.children()]
        return mk_or(kids)
    return exp