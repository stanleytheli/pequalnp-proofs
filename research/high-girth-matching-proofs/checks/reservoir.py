"""Verify cubic completion by attaching one bipartite reservoir per pair of deficits."""
from itertools import combinations
from verify_graph import build, girth, monomials
from regular_complete import bipartition


def incidence(left, right, linked):
    graph = {('L', a): set() for a in left}
    graph.update({('R', b): set() for b in right})
    for a in left:
        for b in right:
            if linked(a, b):
                graph['L', a].add(('R', b))
                graph['R', b].add(('L', a))
    return graph


def reservoirs():
    k33 = incidence(range(3), range(3), lambda a, b: True)
    heawood = incidence(range(7), range(7), lambda a, b: (a-b) % 7 in {0, 1, 3})
    duads = list(combinations(range(6), 2))
    synthemes = [t for t in combinations(duads, 3) if len(set().union(*t)) == 6]
    tutte = incidence(duads, synthemes, lambda d, s: d in s)
    return [('K3,3', k33, 4), ('Heawood', heawood, 6), ('Tutte-Coxeter', tutte, 8)]


def matching_without(reservoir, blocked):
    left = [v for v in reservoir if v[0] == 'L']
    chosen = {}
    def augment(x, seen):
        for y in sorted(reservoir[x]):
            if (x, y) == blocked or y in seen:
                continue
            seen.add(y)
            if y not in chosen or augment(chosen[y], seen):
                chosen[y] = x
                return True
        return False
    for x in left:
        assert augment(x, set())
    assert len(chosen) == len(left) and len(set(chosen.values())) == len(left)
    return {(x, y) for y, x in chosen.items()}


def install(base, reservoir):
    graph = {u: set(vs) for u, vs in base.items()}
    projected = {u: set(vs) for u, vs in base.items()}
    sides = bipartition(base)
    stubs = [[u for u in sorted(base) if sides[u] == color for _ in range(3-len(base[u]))]
             for color in range(2)]
    assert len(stubs[0]) == len(stubs[1])
    x = min(u for u in reservoir if u[0] == 'L')
    y = min(reservoir[x])
    block = x, y
    keep = matching_without(reservoir, block)
    for i, (u, v) in enumerate(zip(*stubs)):
        def node(a):
            return 'reservoir', i, a
        for a in reservoir:
            graph[node(a)] = set()
            projected[node(a)] = set()
        for a in reservoir:
            if a[0] != 'L':
                continue
            for b in reservoir[a]:
                if (a, b) == block:
                    continue
                graph[node(a)].add(node(b))
                graph[node(b)].add(node(a))
                if (a, b) in keep:
                    projected[node(a)].add(node(b))
                    projected[node(b)].add(node(a))
        graph[u].add(node(y)); graph[node(y)].add(u)
        graph[v].add(node(x)); graph[node(x)].add(v)
    return graph, projected


def main():
    for name, reservoir, g in reservoirs():
        assert girth(reservoir) == g and all(len(ns) == 3 for ns in reservoir.values())
        for m, h in [(2, 0), (3, 0), (2, 1)]:
            base, labels = build(m, h)
            graph, projected = install(base, reservoir)
            assert len(bipartition(graph)) == len(graph)
            reached = {next(iter(graph))}
            while True:
                larger = reached | set().union(*(graph[u] for u in reached))
                if larger == reached:
                    break
                reached = larger
            assert len(reached) == len(graph)
            assert all(len(ns) == 3 for ns in graph.values())
            observed = girth(graph)
            assert observed >= min(g, girth(base))
            assert monomials(projected, labels) == monomials(base, labels)
            print(f'reservoir={name} m={m} h={h} N={len(graph)} observed-girth={observed} projection=exact')


if __name__ == '__main__':
    main()
