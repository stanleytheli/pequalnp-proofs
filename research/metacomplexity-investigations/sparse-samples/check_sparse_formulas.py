"""Sparse sample construction, capped formula repair, and independent finite controls."""
from collections import Counter, defaultdict
from functools import lru_cache
from heapq import heappop, heappush
from itertools import combinations
from random import Random


def bit_count(x):
    return bin(x).count("1")


def mask(items):
    return sum(1 << i for i in items)


def subdivision(n, base):
    edges, paths = [], []
    for index, (u, v) in enumerate(base):
        p, q = n + 2*index, n + 2*index + 1
        edges += [(u, p), (p, q), (q, v)]
        paths.append((u, p, q, v))
    return edges, paths


def sample(n, edges):
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    return [
        (mask((u, v)), mask((neighbors[u] | neighbors[v]) - {u, v}))
        for u, v in edges
    ]


def balanced(op, terms):
    if not terms:
        return "zero" if op == "|" else "one"
    if len(terms) == 1:
        return terms[0]
    mid = len(terms)//2
    return (op, balanced(op, terms[:mid]), balanced(op, terms[mid:]))


def star(edges, owners):
    assigned = defaultdict(list)
    for (u, v), owner in zip(edges, owners):
        assert owner in (u, v)
        assigned[owner].append(v if owner == u else u)
    return balanced("|", [("&", owner, balanced("|", group)) for owner, group in assigned.items()])


def from_cover(paths, cover):
    edges, owners = [], []
    for u, p, q, v in paths:
        assert u in cover or v in cover
        tip = q if v not in cover else p
        edges.extend([(u, p), (p, q), (q, v)])
        owners.extend([u if u in cover else p, tip, v if v in cover else q])
    return star(edges, owners)


@lru_cache(None)
def value(node, row):
    if isinstance(node, int):
        return bool(row >> node & 1)
    if isinstance(node, str):
        return node == "one"
    op, a, b = node
    return (value(a, row) and value(b, row)) if op == "&" else (value(a, row) or value(b, row))


def measure(node):
    if isinstance(node, int):
        return 0, Counter([node])
    if isinstance(node, str):
        return 0, Counter()
    a, x = measure(node[1])
    b, y = measure(node[2])
    return a+b+1, x+y


def witness(node, pos, neg):
    assert value(node, pos) and not value(node, neg)
    while isinstance(node, tuple):
        op, a, b = node
        if op == "|":
            node = a if value(a, pos) else b
        else:
            node = b if value(a, neg) else a
    assert isinstance(node, int) and (pos >> node & 1) and not (neg >> node & 1)
    return node


def repair(n, paths, edges, rows, tree, allowed):
    """Return a cap-respecting formula and its recovered old-vertex cover."""
    chosen = []
    errors = 0
    for (p, q), (u, v) in zip(rows, edges):
        good_pos, bad_neg = value(tree, p), value(tree, q)
        errors += int(not good_pos)+int(bad_neg)
        if good_pos and not bad_neg:
            chosen.append(witness(tree, p, q))
        else:
            forbidden = [x for x in (u, v) if x < n and x not in allowed]
            assert len(forbidden) <= 1
            chosen.append(forbidden[0] if forbidden else u)
    centers = set(chosen)
    cover = {i for i in centers if i < n}
    for u, p, q, v in paths:
        if u not in cover and v not in cover:
            assert p in centers and q in centers
            cover.add(u)
    assert all(i in cover for i in range(n) if i not in allowed)
    assert len(cover)+len(paths) <= len(centers)
    return from_cover(paths, cover), cover, errors, star(edges, chosen)


def independent(vertices, edges):
    return not any(mask((u, v)) & vertices == mask((u, v)) for u, v in edges)


def alpha(vertices, edges):
    subset, best = vertices, 0
    while True:
        if independent(subset, edges):
            best = max(best, bit_count(subset))
        if subset == 0:
            return best
        subset = (subset-1) & vertices


def budget_test(n, base, edges):
    """Independently enumerate every physical orientation, updated in Gray order."""
    owners = [u for u, _ in edges]
    degree = Counter(v for edge in edges for v in edge)
    incoming = Counter(owners)
    prev = 0
    exact = [10**9] * (1 << n)
    for i in range(1 << len(edges)):
        gray = i ^ (i >> 1)
        if i:
            e = (gray ^ prev).bit_length()-1
            u, v = edges[e]
            new = v if gray >> e & 1 else u
            incoming[owners[e]] -= 1
            incoming[new] += 1
            owners[e] = new
        need = mask(v for v in range(n) if degree[v]-incoming[v]+int(incoming[v]>0) > 2)
        cost = len(edges)+sum(k>0 for k in incoming.values())-1
        exact[need] = min(exact[need], cost)
        prev = gray
    for v in range(n):
        for u in range(1 << n):
            if u >> v & 1:
                exact[u] = min(exact[u], exact[u ^ (1 << v)])
    expected = [4*len(base)+n-1-alpha(u, base) for u in range(1 << n)]
    assert exact == expected
    base_cost = exact[0]
    assert sum(base_cost-exact[u] == bit_count(u) for u in range(1<<n)) == sum(independent(u, base) for u in range(1<<n))
    return exact


def formula_signatures(n, edges):
    """Exact min leaves for each expressible Boolean signature on these tests."""
    rows = sample(n, edges)
    assignments = [x for x, _ in rows]+[y for _, y in rows]
    target = (1 << len(edges))-1
    columns = [sum(1 << j for j, z in enumerate(assignments) if z >> i & 1) for i in range(n)]
    columns += [0, (1 << len(assignments))-1]
    best, heap, processed = {}, [], []
    for col in set(columns):
        best[col] = 1
        heappush(heap, (1, col))
    while heap:
        size, sig = heappop(heap)
        if best[sig] != size:
            continue
        for b, old in processed:
            v = size+b
            for cand in (sig & old, sig | old):
                if v < best.get(cand, 10**9):
                    best[cand] = v
                    heappush(heap, (v, cand))
        processed.append((size, sig))
    exact = len(edges) + n - alpha((1<<n)-1, edges) - 1
    assert best[target]-1 == exact
    assert min(v-1+2*bit_count(sig^target) for sig, v in best.items()) == exact
    return len(best), exact


def trial_trees(n, base, samples=200):
    rng = Random(88631+n)
    edges, paths = subdivision(n, base)
    physical_n = n + 2*len(base)
    rows = sample(physical_n, edges)
    assert len(set(y for _, y in rows)) == len(edges)
    assert len(set(x for x, _ in rows)) == len(edges)
    assert not set(x for x, _ in rows) & set(y for _, y in rows)
    assert all(bit_count(x) == 2 and 2 <= bit_count(y) <= 3 for x,y in rows)
    assert max(sum(((x>>i)&1)+((y>>i)&1) for x,y in rows) for i in range(physical_n)) <= 6
    assert all(any(x & ~y == 1 << i for x, _ in rows for _, y in rows) for i in range(physical_n))
    def noisy(tree):
        if rng.randrange(15) == 0:
            return rng.choice(["one","zero"])
        if isinstance(tree,tuple):
            op, a, b = tree
            return (op, noisy(a), noisy(b))
        return tree
    for step in range(samples):
        cover = set(range(n))
        for v in rng.sample(range(n), n):
            if rng.choice([True,False]) and all(v not in edge or (edge[0] if edge[1] == v else edge[1]) in cover for edge in base):
                cover.remove(v)
        if step % 2:
            tree = from_cover(paths, cover)
        else:
            tree = star(edges, [rng.choice(edge) for edge in edges])
        if step % 3:
            tree = noisy(tree)
        s, occurrence = measure(tree)
        allowed = {v for v in range(n) if occurrence[v] > 2 or rng.choice([True,False])}
        out, old_cover, bad, direct = repair(n, paths, edges, rows, tree, allowed)
        cost, counts = measure(out)
        assert cost <= s + 2*bad
        assert max(counts.values()) <= 3
        assert all(counts[i] <= (3 if i in allowed else 2) for i in range(physical_n))
        assert all(value(out, x) and not value(out, y) for x, y in rows)
        assert all(u in old_cover or v in old_cover for u,v in base)
        assert len(old_cover) <= s-4*len(base)+1+2*bad
        if not bad:
            direct_cost, direct_reads = measure(direct)
            assert direct_cost <= s
            assert all(direct_reads[i] <= occurrence[i] for i in range(physical_n))
        for _ in range(10):
            row = rng.randrange(1<<physical_n)
            assert value(out,row) == any(row & mask(edge) == mask(edge) for edge in edges)
        value.cache_clear()
    return edges


if __name__ == "__main__":
    complete = list(combinations(range(4), 2))
    cube = [(i, i^(1<<k)) for i in range(8) for k in range(3) if not (i>>k)&1]
    prism = [(i,(i//3)*3+(i+1)%3) for i in range(6)] + [(i, i+3) for i in range(3)]
    k33 = [(i, j) for i in range(3) for j in range(3,6)]
    for n, graph in [(4,complete),(6,prism),(6,k33),(8,cube)]:
        ed = trial_trees(n, graph)
        print(f"{n}-vertex cubic base, {len(ed)*2} labeled rows: 200 randomized exact or noisy formula repairs")
    tab = budget_test(4, complete, subdivision(4, complete)[0])
    print("K4: 262144 orientations, 16 cap allocations; optimal sizes:", tab)
    for n in (5,6):
        states, exact = formula_signatures(n, [(i,(i+1)%n) for i in range(n)])
        print(f"C{n}: all {states} reachable sample signatures checked, optimum {exact} gates, penalty-2 optimum {exact}")
