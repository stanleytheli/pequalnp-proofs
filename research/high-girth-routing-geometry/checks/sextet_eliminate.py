"""Recheck a sextet permanent projection by directed vertex elimination.

This verifier never enumerates dense permutations. Each matrix entry is a
dictionary encoding a polynomial in independent variables over the naturals.
A legal elimination is an identity over every commutative semiring.
"""
from collections import Counter
from sextet import sextet
from sextet_routes import attempt, contract

ONE = {():1}

def product(left, right):
    result = Counter()
    for a, count_a in left.items():
        for b, count_b in right.items():
            result[tuple(sorted(a+b))] += count_a*count_b
    return result

def projection(p, m, generator=attempt):
    graph = sextet(p)
    forward, backward, matching = contract(graph)
    for seed in range(128):
        model = generator(m, forward, backward, seed)
        if model:
            break
    else:
        raise AssertionError("No routing found")
    centers, paths, links = model
    active = set(centers)
    for word in paths.values():
        active.update(word)
    matrix = {v:{v:ONE.copy()} for v in active}
    for i, center in enumerate(centers):
        matrix[center][center] = {((i,i),):1}
    for word in paths.values():
        for v,w in zip(word,word[1:]):
            assert w!=v and matching[w] in graph[v]
            matrix[v][w] = ONE.copy()
    for label,link in links.items():
        v,w=link[:2]
        assert matrix[v][w]==ONE
        matrix[v][w]={ (label,):1 }
    return graph,matching,centers,matrix

def prune(matrix, centers):
    """Use the unit-loop rule in one orientation at each step."""
    todo = set(matrix)-set(centers)
    stats = Counter()
    while todo:
        # Filter the actual transition table again at each elimination.
        transposed = {v:[] for v in matrix}
        for u,row in matrix.items():
            for v in row:
                if u!=v:
                    transposed[v].append(u)
        for v in sorted(todo):
            src = transposed[v]
            dst = [w for w in matrix[v] if w!=v]
            if len(src)<=1 or len(dst)<=1:
                break
        else:
            raise AssertionError("No legal butterfly elimination")
        assert matrix[v][v]==ONE
        stats["single predecessor" if len(src)<=1 else "single successor"]+=1
        for x in src:
            for y in dst:
                total=Counter(matrix[x].get(y,{}))
                total.update(product(matrix[x][v],matrix[v][y]))
                matrix[x][y]=total
        for x in src:
            del matrix[x][v]
        del matrix[v]
        todo.remove(v)
    return stats

def verify(p,m):
    graph,matching,centers,matrix=projection(p,m)
    active=len(matrix)
    summary=prune(matrix,centers)
    # All originally unused pairs keep only their own unit matching edge.
    unused=len(matching)-active
    for i,x in enumerate(centers):
        assert set(matrix[x])==set(centers)
        for j,y in enumerate(centers):
            assert matrix[x][y]=={((i,j),):1}
    print(f'p={p} physical_vertices={len(graph)} dense_dimension={m} '
          f'isolated_unit_pairs={unused} active_pairs={active} '
          f'predecessor_pivots={summary["single predecessor"]} '
          f'successor_pivots={summary["single successor"]} verified_entries={m*m}')

if __name__=="__main__":
    verify(41,5)
    verify(73,7)
