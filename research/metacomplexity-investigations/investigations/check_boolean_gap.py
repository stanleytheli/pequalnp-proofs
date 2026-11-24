"""Structural and truth-table controls for the read-two succinct MCSP reduction."""
from collections import Counter
from itertools import combinations, product
import random
from pair_trees import compile_cnf


def graphs(t):
    def port(a,b,j):
        return 8*((a%t)*t+b%t)+j
    matching = []
    stars = []
    for a,b in product(range(t),repeat=2):
        moves = ((a+2*b,b),(a+2*b+1,b),(a,b+2*a),(a,b+2*a+1))
        for j,(c,d) in enumerate(moves):
            matching.append(tuple(sorted((port(a,b,j),port(c,d,j+4)))))
        stars.extend((port(a,b,0),port(a,b,j)) for j in range(1,8))
    endpoints = Counter(v for edge in matching for v in edge)
    assert len(endpoints) == 8*t*t and set(endpoints.values()) == {1}
    return matching,stars


def crossing_checks():
    rng = random.Random(2101)
    checks = 0
    for t in (1,2,4,6,8):
        match,stars = graphs(t)
        graph = set(match+stars)
        n = 8*t*t
        adj = [set() for _ in range(n)]
        for u,v in graph:
            assert u != v
            adj[u].add(v)
            adj[v].add(u)
        assert max(map(len,adj)) <= 8
        if t==1:
            sets = [set(s) for k in range(3,6) for s in combinations(range(n),k)]
        else:
            sets = [set(rng.sample(range(n),rng.randrange((n+2)//3,2*n//3+1))) for _ in range(70)]
            # Entire clusters on either side exercise the external-matching case.
            for _ in range(20):
                groups = rng.sample(range(t*t),t*t//2)
                sets.append({8*g+i for g in groups for i in range(8)})
        for side in sets:
            cross = [(u,v) for u,v in sorted(graph) if (u in side) != (v in side)]
            assert len(cross) >= (8-5*(2**.5))*n/1536
            forbidden = set()
            chosen = set()
            for u,v in cross:
                if u not in forbidden and v not in forbidden:
                    chosen.add((u,v))
                    forbidden |= {u,v} | adj[u] | adj[v]
            assert len(chosen)*128 >= len(cross)
            vertices = {v for edge in chosen for v in edge}
            assert {(u,v) for u,v in graph if u in vertices and v in vertices} == chosen
            checks += 1
    return checks


def selector_check(n,clauses):
    used = Counter()
    port_clauses = []
    for clause in clauses:
        ports = []
        for variable in clause:
            assert used[variable] < 2
            ports.append(4*(abs(variable)-1)+2*int(variable<0)+used[variable])
            used[variable] += 1
        port_clauses.append(ports)
    assert len({p for clause in port_clauses for p in clause}) == sum(map(len,clauses))
    sat = any(all(any(assignment[abs(l)-1] == (l>0) for l in clause) for clause in clauses)
              for assignment in product((0,1),repeat=n))
    def clash(mask):
        return any((mask >> (4*i) & 3) and (mask >> (4*i+2) & 3) for i in range(n))
    def guard(mask):
        return all(any(mask >> j & 1 for j in clause) for clause in port_clauses)
    safe = next((p for p in range(1 << (4*n)) if guard(p) and not clash(p)),None)
    assert bool(safe is not None) == sat
    for v in range(4*n):
        other = 4*(v//4) + (2 if v%4 < 2 else 0)
        assert not clash(1 << other) and clash((1 << other)|(1 << v))
    match,stars = graphs(1)
    def edge(x,edges):
        return any(x >> i & 1 and x >> j & 1 for i,j in edges)
    E = [edge(x,match) for x in range(256)]
    G = [edge(x,match+stars) for x in range(256)]
    H = [edge(x,stars) for x in range(256)]
    assert not guard(0) and not clash(0)
    assert E != G
    if safe is not None:
        assert [bool(clash(safe) or e or (guard(safe) and h)) for e,h in zip(E,H)] == G
    else:
        # The two graph-bit possibilities e=0,h=1 and e=h=0 suffice
        # for every selector. Check all four abstract combinations.
        for p in range(1 << (4*n)):
            for e,h in product((False,True),repeat=2):
                assert (clash(p) or e or (guard(p) and h)) == (clash(p) or e)
    return sat


def leaf_order(tree):
    if isinstance(tree,int):
        return [tree]
    return leaf_order(tree[1])+leaf_order(tree[2])


def evaluate(tree,ones):
    if isinstance(tree,int):
        return tree in ones
    if tree[0]=="and":
        return evaluate(tree[1],ones) and evaluate(tree[2],ones)
    return evaluate(tree[1],ones) or evaluate(tree[2],ones)


def shape(tree):
    if isinstance(tree,int):
        return "*"
    return (tree[0],shape(tree[1]),shape(tree[2]))


def fixed_trees():
    sources = [[(1,),(-1,)],[(1,2),(-1,2)],[(1,2,3),(-2,1,-3)],[(1,1,-1)],[]]
    K = max(compile_cnf(s)[0]["selector_copies"] for s in sources)
    reference = None
    checked = 0
    for s in sources:
        compiled,logical = compile_cnf(s,K)
        n = compiled["input_count"]
        A,B = compiled["first"],compiled["second"]
        assert sorted(leaf_order(A)) == sorted(leaf_order(B)) == list(range(n))
        current = A,shape(B),leaf_order(B)[4*K:]
        if reference is None:
            reference = current
        assert current == reference
        for bits in product((0,1),repeat=max(logical)):
            satisfied = all(any(bits[abs(l)-1]==(l>0) for l in c) for c in s)
            ones = {4*i+2*int(not bits[v-1])+j for i,v in enumerate(logical) for j in range(2)}
            # Choose just one internal center/leaf pair never externally matched.
            ones |= {4*K,4*K+1}
            assert not evaluate(A,ones)
            assert evaluate(B,ones) == satisfied
            checked += 1
    return checked


if __name__ == "__main__":
    cuts = crossing_checks()
    pool = [(1,),(-1,),(2,),(-2,),(1,2),(1,-2),(-1,2),(-1,-2)]
    totals = Counter()
    for k in range(1,5):
        for clauses in combinations(pool,k):
            if max(Counter(l for c in clauses for l in c).values()) <= 2:
                totals[selector_check(2,clauses)] += 1
    print(f"{cuts} balanced data cuts: crossing counts and whole-graph induced matchings checked")
    print(f"{totals[True]} SAT and {totals[False]} UNSAT port formulas: selectors, restrictions and essentiality checked")
    print(f"fixed pair of tree shapes: {fixed_trees()} complete assignment restrictions across five differently wired instances")
