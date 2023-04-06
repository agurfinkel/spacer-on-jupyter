"""Verification Condition Generation."""

import z3

from .ts import mk_seq


def vc_gen(T):
    """Verification Condition (VC) for an Inductive Invariant."""
    Inv = z3.Function('Inv', *(T.sig() + [z3.BoolSort()]))

    InvPre = Inv(*T.pre_vars())
    InvPost = Inv(*T.post_vars())

    all_vars = T.all()
    vc_init = z3.ForAll(all_vars, z3.Implies(T.Init, InvPre))
    vc_ind = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, T.Tr), InvPost))
    vc_bad = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, T.Bad),
                                            z3.BoolVal(False)))
    return [vc_init, vc_ind, vc_bad], InvPre


def vc_gen_bwd(T):
    """Verification Condition (VC) for Backward Inductive Invariant."""
    Inv = z3.Function('BwdInv', *(T.sig() + [z3.BoolSort()]))

    InvPre = Inv(*T.pre_vars())
    InvPost = Inv(*T.post_vars())

    all_vars = T.all()
    vc_init = z3.ForAll(all_vars, z3.Implies(T.Bad, InvPre))
    vc_ind = z3.ForAll(all_vars, z3.Implies(z3.And(InvPost, T.Tr), InvPre))
    vc_bad = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, T.Init),
                                            z3.BoolVal(False)))

    return [vc_init, vc_ind, vc_bad], InvPre


def vc_gen_2ind(T):
    """Verification condition for 2-inductive invariant."""
    Inv = z3.Function('2Inv', *(T.sig() + [z3.BoolSort()]))

    InvPre = Inv(*T.pre_vars())
    InvPost = Inv(*T.post_vars())

    all_vars = T.all()
    # Inv contains initial states
    vc_init1 = z3.ForAll(all_vars, z3.Implies(T.Init, InvPre))
    # Inv contains states reachable in one step
    vc_init2 = z3.ForAll(all_vars, z3.Implies(z3.And(T.Init, T.Tr), InvPost))

    # Inv is stable under two steps of Tr , assuming Inv holds after first step
    TSeq = mk_seq(T, T, constraint=InvPre)
    InvPost = Inv(*TSeq.post_vars())
    all_vars = TSeq.all()
    vc_ind = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, TSeq.Tr), InvPost))

    # Inv does not satisfy Bad
    vc_bad = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, T.Bad),
                                            z3.BoolVal(False)))

    return [vc_init1, vc_init2, vc_ind, vc_bad], InvPre


def cfa_vc_gen(A):
    """Verification Condition (VC) for a Control Flow Automaton."""
    all_vars = A.all()
    sig = A.sig() + [z3.BoolSort()]

    Invs = dict()
    for n in A.nodes:
        inv = z3.Function(str(n), *sig)
        Invs[n] = inv

    Entry = Invs[A.entry]
    Exit = Invs[A.exit]

    vc = list()
    vc.append(z3.ForAll(all_vars, Entry(*A.pre_vars())))

    for (k, v) in A.edges.items():
        src, dst = k
        srcP, dstP = Invs[src], Invs[dst]

        head = dstP(*A.post_vars())
        sPred = srcP(*A.pre_vars())
        vc.append(z3.ForAll(all_vars, z3.Implies(z3.And(sPred, v), head)))
    vc.append(z3.ForAll(all_vars,
                        z3.Implies(Exit(*A.pre_vars()), z3.BoolVal(False))))
    return vc, {n: Invs[n](A.pre_vars()) for n in A.nodes}
