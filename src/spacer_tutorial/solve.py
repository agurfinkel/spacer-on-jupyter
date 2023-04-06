"""Solver wrapper"""
import z3

from .fml import free_arith_vars

def solve_horn(chc, pp=False, q3=False, gg=True, max_unfold=10, verbosity=0):
    """Wrapper to solve CHC and extract results.

        pp controls pre-processing (default: off)
        q3 controls quantified invariants (default: off)
        gg controls global guidance (default: true)
        max_unfold limits depth of search (default: 10 levels)
        verbosity controls debug output from the solver (default: 0)
    """
    z3.set_param(verbose=verbosity)

    s = z3.SolverFor('HORN')
    s.set('engine', 'spacer')
    s.set('spacer.order_children', 2)


    # Enable/disable global guidance strategy
    s.set('spacer.global', gg)

    # Disable pre-processing. 
    # Disabling simplifies interpreting results, but it required for many harder instances
    if not pp:
        s.set('xform.inline_eager', False)
        s.set('xform.inline_linear', False)
        s.set('xform.slice', False)

    # Limit unfolding. Solver will return with unknown if maximum unfolding level is reached
    if max_unfold > 0:
        s.set('spacer.max_level', max_unfold)

    # Enable quantifiers. This is still quite experimental
    if q3:
        # allow quantified variables in pobs
        s.set('spacer.ground_pobs', False)
        # enable quantified generalization
        s.set('spacer.q3.use_qgen', True)

    # From this point on, solver is configured and solving begins

    # add constraints to solver
    s.add(chc)

    if verbosity > 0:
        print(s.sexpr())

    # run solver. This might take a while.
    res = s.check()

    # Extract either the model or unsat proof, based on the result 
    answer = None
    if res == z3.sat:
        answer = s.model()
    elif res == z3.unsat:
        answer = s.proof()

    # return the sat/unsat/unknown result and a certificate (model/proof)
    return res, answer


def interpolate(A, B, verbosity=0):
    '''Computes a binary Craig interpolant between A and B'''
    As = free_arith_vars(A)
    Bs = free_arith_vars(B)

    shared = [s for s in As & Bs]

    # Uninterpreted predicate Itp over shared symbols
    Itp = z3.Function('Itp', [s.sort() for s in shared] + [z3.BoolSort()])

    # first CHC: A ==> Itp
    left = z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
    # second CHC: Itp ==> !B
    right = z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))

    # run CHC solver
    res, answer = solve_horn([left, right])

    if res == z3.sat:
        return answer.eval(Itp(shared))

    return None
