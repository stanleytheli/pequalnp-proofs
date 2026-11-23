"""Independent-set corner limit for a literal-labeled directed nonreachability test."""
from dataclasses import dataclass, field


@dataclass
class Graph:
    labels: list = field(default_factory=list)
    edges: list = field(default_factory=list)

    def vertex(self, label):
        # Integer 0 is always active; None is never active; +/-i denotes x_i or 1-x_i.
        self.labels.append(label)
        return len(self.labels)-1

    def edge(self, u, v):
        self.edges.append((u, v))


def complement(label):
    if label is None:
        return 0
    if label == 0:
        return None
    return -label


def active(label, bits):
    return label == 0 or label is not None and bits[abs(label)-1] == (label>0)


def construct(n, arcs, source=0, target=None):
    if target is None:
        target = n-1
    if source == target:
        raise ValueError("distinct distinguished vertices required")
    g, left, right = Graph(), {}, {}
    for v in range(n):
        if v != target:
            left[v] = g.vertex(0)
        if v != source:
            right[v] = g.vertex(0)
        if v not in (source, target):
            g.edge(left[v], right[v])
    default = n-2
    for u, v, literal in arcs:
        if u == target or v == source:
            continue
        if u not in left or v not in right:
            raise ValueError("unknown directed vertex")
        a, b = g.vertex(literal), g.vertex(literal)
        g.edge(left[u], a)
        g.edge(b, a)
        g.edge(b, right[v])
        c, d = g.vertex(complement(literal)), g.vertex(complement(literal))
        g.edge(c,d)
        default += 1
    return g, default


def reachable(n, arcs, bits):
    stack, visited = [0], {0}
    while stack:
        v = stack.pop()
        for s, t, label in arcs:
            if s == v and active(label, bits) and t not in visited:
                visited.add(t)
                stack.append(t)
    return n-1 in visited


def matching(graph, bits):
    # Edges are stored in left,right order. This augmenting-path code operates
    # on the emitted graph and does not use the original directed arcs.
    chosen = [active(label, bits) for label in graph.labels]
    adj = {}
    for u,v in graph.edges:
        if chosen[u] and chosen[v]:
            adj.setdefault(u,[]).append(v)
    pair_right = {}
    def try_left(v, seen):
        for w in adj[v]:
            if w in seen:
                continue
            seen.add(w)
            if w not in pair_right or try_left(pair_right[w], seen):
                pair_right[w] = v
                return True
        return False
    return sum(try_left(v,set()) for v in adj)


def diamonds(k):
    return k+1, [(i,i+1,label) for i in range(k)
                 for label in (2*i+1,2*i+2)]
