import graphviz

def xnet_graph():
    g = graphviz.Source("""
digraph G {

  x0 -> v0 [label="0.1"]
  x0 -> v1 [label="-4.3"]
  x0 -> v2 [label="4.2"]
  
  x1 -> v0 [label="-0.6"]
  x1 -> v1 [label="4.4"]
  x1 -> v2 [label="-4.2"]

  v0 -> v3 [label="ReLU"]
  v1 -> v4 [label="ReLU"]
  v2 -> v5 [label="ReLU"]
  
  v3 -> y0 [label="0.4"]
  v3 -> y1 [label="-0.4"]
  
  v4 -> y0 [label="-4.9"]
  v4 -> y1 [label="3.9"]
  
  v5 -> y0 [label="3.9"]
  v5 -> y1 [label="4.6"]
}
""")
    return g

