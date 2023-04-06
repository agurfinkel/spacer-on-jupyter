"""CHCs for Lamport's Bakery Algorithm."""

import z3
from .ts import Ts


def mk_bakery(num_procs=3):
    """Create Ts for Bakery protocol with 3 participants."""
    T = Ts('Bakery')
    ZZ = z3.IntSort()
    State, State_out = T.add_var(z3.ArraySort(ZZ, ZZ), name='State')
    Num, Num_out = T.add_var(z3.ArraySort(ZZ, ZZ), name='Num')
    Issue, Issue_out = T.add_var(ZZ, name='Issue')
    Serve, Serve_out = T.add_var(ZZ, name='Serve')
    i = T.add_input(ZZ, name='i')
    j = T.add_input(ZZ, name='j')

    # initial condition
    T.Init = z3.And(Issue == 0, Serve == 0,
                    State[1] == 0, State[2] == 0, State[3] == 0,
                    Num[1] == -1, Num[2] == -1, Num[3] == -1)
    # transition from state0 by process i
    ts_state0 = z3.And(State[i] == 0, 1 <= i, i <= num_procs,
                       Serve_out == Serve, Issue_out == Issue + 1,
                       State_out == z3.Update(State, i,  1),
                       Num_out == z3.Update(Num, i, Issue))
    # transition from state1 by process i
    ts_state1 = z3.And(State[i] == 1, 1 <= i, i <= num_procs,
                       Num[i] == Serve, Serve_out == Serve,
                       Issue_out == Issue,
                       Num_out == Num,
                       State_out == z3.Update(State, i,  2))
    # transition from state2 by process i
    ts_state2 = z3.And(State[i] == 2, 1 <= i, i <= num_procs,
                       Issue_out == Issue, Serve_out == Serve + 1,
                       Num_out == z3.Update(Num, i, -1),
                       State_out == z3.Update(State, i,  0))
    T.Tr = z3.Or(ts_state0, ts_state1, ts_state2)
    T.Bad = z3.And(State[i] == 2, State[j] == 2, i != j,
                   1 <= i, i <= num_procs, 1 <= j, j <= num_procs)
    return T
