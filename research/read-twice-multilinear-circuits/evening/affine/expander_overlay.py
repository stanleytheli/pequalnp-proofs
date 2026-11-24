"""Add an explicit bounded-degree expander to a weighted seed without changing it.

An activity-zero helper on each added edge makes the two-edge connection
invisible to the weighted independent-set partition function. The unsigned
graph of the multilinear extension retains its physical edges.
"""
from math import isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'graph-transfer'))
from hamiltonian_seed import WeightedGraph


def margulis(side):
    """Underlying simple graph of the eight-neighbor Gabber–Galil multigraph."""
    edges = set()
    for x in range(side):
        for y in range(side):
            u = side*x+y
            for a,b in ((x+2*y,y),(x+2*y+1,y),(x,y+2*x),(x,y+2*x+1)):
                v = side*(a%side)+(b%side)
                if u != v:
                    edges.add(tuple(sorted((u,v))))
    return sorted(edges)


def overlay(base):
    """Input is already degree-split; keep its designated data leaves private."""
    assert max(base.degrees()) <= 3
    graph = WeightedGraph(base.labels.copy(),base.edges.copy())
    roots = [i for i,c in enumerate(graph.labels) if not isinstance(c,tuple)]
    data = {i for i,c in enumerate(graph.labels) if isinstance(c,tuple)}
    assert all(graph.labels[i][0]=='prob' for i in data)
    degrees = graph.degrees()
    assert all(degrees[i]==1 for i in data)
    side = isqrt(len(roots)-1)+1
    while len(roots) < side*side:
        roots.append(graph.vertex(0))
    for a,b in margulis(side):
        hidden = graph.vertex(0)
        graph.edge(roots[a],hidden)
        graph.edge(roots[b],hidden)
    assert max(graph.degrees()) <= 11
    return graph
