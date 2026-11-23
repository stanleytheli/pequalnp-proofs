"""One verifiable incidence witness per vertex of a graph with cyclic components.

The indices returned by incident_matching are exactly the 'edge' injection
in the Lean lower bound. Parallel edges are permitted. No network or packages.
"""


def incident_matching(vertex_count, edges):
    adjacency = [[] for _ in range(vertex_count)]
    for index, (u, v) in enumerate(edges):
        if not (0 <= u < vertex_count and 0 <= v < vertex_count) or u == v:
            raise ValueError("edges need two distinct valid endpoints")
        adjacency[u].append((v, index))
        adjacency[v].append((u, index))
    result = [-1] * vertex_count
    seen = set()
    tree_edges = set()
    for start in range(vertex_count):
        if start in seen:
            continue
        stack, component = [start], [start]
        seen.add(start)
        extra = None
        while stack:
            u = stack.pop()
            for v, edge in adjacency[u]:
                if v not in seen:
                    seen.add(v)
                    tree_edges.add(edge)
                    stack.append(v)
                    component.append(v)
                elif edge not in tree_edges:
                    extra = edge
        if extra is None:
            raise ValueError(f"acyclic component containing vertex {start}")
        root = edges[extra][0]
        result[root] = extra
        stack = [root]
        while stack:
            u = stack.pop()
            for v, edge in adjacency[u]:
                if edge in tree_edges and result[v] == -1:
                    result[v] = edge
                    stack.append(v)
        if any(result[v] == -1 for v in component):
            raise AssertionError("incomplete spanning-tree orientation")
    verify(vertex_count, edges, result)
    return result


def verify(vertex_count, edges, owners):
    if len(owners) != vertex_count or len(set(owners)) != vertex_count:
        raise ValueError("each vertex must receive a distinct edge")
    if any(not 0 <= edge < len(edges) or v not in edges[edge]
           for v, edge in enumerate(owners)):
        raise ValueError("an owned edge must be incident to its owner")


if __name__ == "__main__":
    from hamiltonian_seed import hc_seed, split_degree
    from fair_metric import signed_cnf
    from fair_counting import attach_tails
    for n in (2, 3, 4, 5):
        graph = split_degree(hc_seed(n, probability_leaves=True))
        owners = incident_matching(len(graph.labels), graph.edges)
        lower = 14 * len(graph.edges) + len(owners) - 1
        print(f"HC n={n} base vertices={len(owners)} edges={len(graph.edges)} 10-subdivision exact gates={lower}")
    cnf, _ = signed_cnf(3, [(1, -2), (2, 3), (-3, 1)])
    graph = attach_tails(cnf, 6)
    incident_matching(len(graph.labels), graph.edges)
    for edges in [[(0, 1)], [(0, 1), (2, 3)]]:
        try:
            incident_matching(max(max(e) for e in edges) + 1, edges)
        except ValueError:
            continue
        raise AssertionError("accepted an acyclic component")
