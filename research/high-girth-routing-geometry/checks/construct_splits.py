"""Turn routed branch trees and disjoint private links into permanent-preserving splits.

Trees grow from the center first. Each new outgoing child moves only its
descendants' target centers, and each incoming child moves only its
descendants' already distinct outgoing ports. At the end each private link
is subdivided one vertex at a time. This algorithm needs no pivot search.
"""
from collections import defaultdict


def compile_routing(centers, paths, links):
    roots = set(centers)
    assert len(roots) == len(centers) and set(paths) == set(links)
    m = len(centers)
    assert all((i, j) in paths or i == j for i in range(m) for j in range(m))
    nodes = [dict(), dict()]
    descendants = [defaultdict(list), defaultdict(list)]
    private = set()
    ordered = sorted(paths)
    ports = [{}, {}]
    for pos in ordered:
        i, j = pos
        path, link = tuple(paths[pos]), tuple(links[pos])
        assert 0 <= i < m and 0 <= j < m and len(link) >= 2
        assert path[0] == centers[i] and path[-1] == centers[j]
        x = path.index(link[0])
        assert path[x:x+len(link)] == link
        trunks = (path[:x+1], path[x+len(link)-1:][::-1])
        assert len(link) == len(set(link)) and not private.intersection(link)
        private.update(link)
        for side, trunk in enumerate(trunks):
            assert len(trunk) >= 2 and len(trunk) == len(set(trunk))
            ports[side][pos] = trunk[-1]
            for depth, (a, b) in enumerate(zip(trunk, trunk[1:]), start=1):
                assert b not in roots
                assert nodes[side].setdefault(b, (depth, a)) == (depth, a)
                descendants[side][b].append(pos)
    assert set(nodes[0]).isdisjoint(nodes[1])
    assert not private.intersection(roots)
    for side in (0, 1):
        terminal = set(ports[side].values())
        assert len(terminal) == len(ports[side])
        assert terminal == private.intersection(nodes[side])
        assert all(len(descendants[side][leaf]) == 1 for leaf in terminal)

    steps = []
    for side in (0, 1):
        # Dictionary insertion order provides deterministic ties without
        # imposing an ordering on the physical vertex type.
        for b, (_, a) in sorted(nodes[side].items(), key=lambda kv:kv[1][0]):
            labels = descendants[side][b]
            moved = [centers[j] for _,j in labels] if side == 0 else [ports[0][p] for p in labels]
            assert len(set(moved)) == len(moved)
            steps.append((side == 0, a, b, moved))
    for pos in ordered:
        link = links[pos]
        for a,b in zip(link[:-2], link[1:-1]):
            steps.append((True, a, b, [link[-1]]))
    return steps


def verify(prime, m):
    from adaptive_routes import route
    from sextet import sextet
    from sextet_routes import contract
    graph = sextet(prime)
    fw, bw, matching = contract(graph)
    model = next(x for seed in range(128) if (x:=route(m,fw,bw,seed)) is not None)
    centers, paths, links = model
    steps = compile_routing(centers, paths, links)
    labels = {(a,b):(i,j) for i,a in enumerate(centers) for j,b in enumerate(centers)}
    names = set(centers)
    for out,a,b,moved in steps:
        assert a in names and b not in names
        names.add(b)
        for z in moved:
            old = (a,z) if out else (z,a)
            new = (b,z) if out else (z,b)
            assert new not in labels
            labels[new] = labels.pop(old)
        forward = (a,b) if out else (b,a)
        assert (b,b) not in labels and forward not in labels
        labels[b,b] = labels[forward] = 1
    assert all(matching[b] in graph[a] for a,b in labels)
    for i in range(m):
        for j in range(m):
            where = tuple(links[i,j][-2:]) if (i,j) in links else (centers[i],centers[i])
            assert labels[where] == (i,j)
    assert sorted(v for v in labels.values() if v != 1) == [(i,j) for i in range(m) for j in range(m)]
    print(f"p={prime} dimension={m} forward_only_splits={len(steps)} physical_entries={len(labels)}")


if __name__ == "__main__":
    verify(41, 10)
    verify(73, 20)
