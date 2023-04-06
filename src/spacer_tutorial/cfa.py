"""Control Flow Automata."""
import graphviz
from .ts import Ts

class CFA(object):
    """Control Flow Automaton.

    An automation whose nodes are annotated with transition relations
   """ 
    def __init__(self, name):
        self._base = Ts(name)

        self.entry = None
        self.exit = None
        self.edges = dict()
        self.nodes = set()

    def sig(self):
        return self._base.sig()

    def inputs(self):
        return self._base.inputs()

    def pre_vars(self):
        return self._base.pre_vars()

    def post_vars(self):
        return self._base.post_vars()

    def vars(self):
        return self._base.vars()

    def pre_post_vars(self):
        return self._base.pre_post_vars()

    def all(self):
        return self._base.all()

    def add_var(self, sort, name=None):
        return self._base.add_var(sort, name)

    def add_input(self, sort, name=None):
        return self._base.add_input(sort, name)

    def to_post(self, e):
        return self._base.to_post(e)

    def add_edge(self, src, dst, tr):
        self.nodes.add(src)
        self.nodes.add(dst)
        self.edges[(src, dst)] = tr

    def set_entry_node(self, n):
        self.nodes.add(n)
        self.entry = n
 
    def set_exit_node(self, n):
        self.nodes.add(n)
        self.exit = n

    def is_entry_node(self, n):
        return n == self.entry

    def is_exit_node(self, n):
        return n == self.exit

    def to_dot(self):
        g = graphviz.Digraph()

        for n in self.nodes:
            g.node(str(n), str(n))

        for (k, v) in self.edges.items():
            src, dst = k
            g.edge(str(src), str(dst), label=str(v))

        return g
