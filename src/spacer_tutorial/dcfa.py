"""Data-Flow and Control-Flow Automaton."""
import z3

from .cfa import CFA

class DCFA(CFA):
    def __init__(self, name):
        super().__init__(name)
        self._named_pack_vars = dict()
        self._pack_vars = list()
        self._pack_var_names = list()

    def all(self):
        return super().all() + self.pack_vars()

    def packed_sig(self):
        return [v.sort() for v in self._pack_vars]

    def add_pack_var(self, sort, name=None):
        vname = self._new_pack_var_name(name=name)
        v = z3.Const(vname, sort)
        self._pack_vars.append(v)
        self._pack_var_names.append(name)
        if name is not None:
            self._named_pack_vars[name] = v
        return v

    def get_pack_var(self, idx):
        if isinstance(idx, int):
            return self._pack_vars[idx]
        elif idx in self._named_pack_vars:
            return self._named_pack_vars[idx]
        return None

    def pack_vars(self):
        return self._pack_vars

    def get_pack_var_name(self, idx):
        if idx < len(self._pack_var_names):
            return self._pack_var_names[idx]
        return None

    def _new_pack_var_name(self, name):
        if name is not None:
            return str(name)
        else:
            idx = len(self._pack_vars)
            return 'p_' + str(idx)


class PackTr(object):
    """Assignment of state/input expressions into packed variables."""

    def __init__(self, *sub):
        self.sub = sub

    def __repr__(self):
        body = ' '.join([str(lhs) + ':=' + str(rhs) for (lhs, rhs) in self.sub])
        return 'pack(' + body + ')'


class UnpackTr(object):
    """Assignment from packed variables to state/input variables."""

    def __init__(self, *sub):
        self.sub = sub

    def __repr__(self):
        body = ' '.join([str(lhs) + ':=' + str(rhs) for (lhs, rhs) in self.sub])
        return 'unpack(' + body + ')'


def dcfa_vc_gen(A):
    """Verification Condition for a Data-Flow and Control Flow Automaton."""

    all_vars = A.all()
    sig = A.sig() + [z3.BoolSort()]

    Invs = dict()
    for n in A.nodes:
        inv = z3.Function(str(n), *sig)
        Invs[n] = inv

    Entry = Invs[A.entry]
    Exit = Invs[A.exit]

    # predicate for packed variables
    Pack = z3.Function('Pack', *(A.packed_sig() + [z3.BoolSort()]))
    # applied predicate
    Packed = Pack(A.pack_vars())

    vc = list()
    vc.append(z3.ForAll(all_vars, Entry(*A.pre_vars())))

    for (k, tr) in A.edges.items():
        src, dst = k
        srcP, dstP = Invs[src], Invs[dst]

        if isinstance(tr, PackTr):
            # add clause defining Packed
            body = [srcP(*A.pre_vars())] + [p == x for (p, x) in tr.sub]
            vc.append(z3.ForAll(all_vars, z3.Implies(z3.And(*body), Packed)))

            # no-op for control-flow transition
            tr = z3.And(*[v == v_out for (v, v_out) in A.pre_post_vars()])
        elif isinstance(tr, UnpackTr):
            # body depends on the packed predicate
            body = [Packed]
            unpacked = set()
            # generate equalities for unpacked variables
            for x, p in tr.sub:
                unpacked.add(id(x))
                x_out = A.to_post(x)
                body.append(x_out == p)
            # all other variables are preserved over the transition
            for v, v_out in A.pre_post_vars():
                if id(v) not in unpacked:
                    body.append(v_out == v)
            tr = z3.And(*body)

        head = dstP(*A.post_vars())
        loc = srcP(*A.pre_vars())
        vc.append(z3.ForAll(all_vars, z3.Implies(z3.And(loc, tr), head)))

    vc.append(z3.ForAll(all_vars,
                        z3.Implies(Exit(*A.pre_vars()), z3.BoolVal(False))))
    return vc, {n: Invs[n](A.pre_vars()) for n in A.nodes}, Packed
