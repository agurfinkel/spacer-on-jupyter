"""Proof processing."""
import graphviz


class SpacerProof(object):

    def __init__(self, pf_ast):
        # strip off last mp to false
        self._ast = pf_ast.children()[0]

    def _get_fact(self, ast):
        return ast.children()[-1]

    def _to_dot_rec(self, ast, graph, visited):
        """Recursively convert proof to DOT graph."""
        if ast.get_id() in visited:
            return

        visited.add(ast.get_id())

        dst = str(self._get_fact(ast).get_id())
        kids = ast.children()
        for k in kids[1:-1]:
            k_fact = self._get_fact(k)
            if k_fact.get_id() not in visited:
                graph.node(str(k_fact.get_id()), str(k_fact))
                visited.add(k_fact.get_id())
                self._to_dot_rec(k, graph, visited)
            graph.edge(str(k_fact.get_id()), dst)

    def to_dot(self):
        """Convert proof to DOT graph."""
        g = graphviz.Digraph()

        visited = set()

        fact = self._get_fact(self._ast)
        id = fact.get_id()
        g.node(str(id), str(fact))
        visited.add(id)
        self._to_dot_rec(self._ast, g, visited)
        return g

    def _repr_mimebundle_(self, include, exclude, **kwargs):
        """Return Jupyter representation of the graph."""
        return self.to_dot()._repr_mimebundle_(include, exclude, **kwargs)

    def __str__(self):
        return str(self.to_dot())
    
    def raw(self):
        return self._ast
