"""Exact finite controls for the universal lift for bipartite multigraphs.

Labels are not sampled: all incidence patterns realizable as an OR of source
edges, with complementary OR, are tested. Each span check uses exact rationals.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import lcm


def perfect(n, edges):
    by_cell = defaultdict(list)
    for e, (a,b) in edges.items():
        by_cell[a,b].append(e)
    return [frozenset(t) for p in permutations(range(n)) for t in product(*(by_cell[i,p[i]] for i in range(n)))]


def restrict(edges, left, right):
    il = {v:i for i,v in enumerate(sorted(left))}
    ir = {v:i for i,v in enumerate(sorted(right))}
    return {e:(il[a],ir[b]) for e,(a,b) in edges.items() if a in left and b in right}


def components(n, edges):
    nbr = defaultdict(set)
    for a,b in edges.values():
        nbr[a].add(n+b)
        nbr[n+b].add(a)
    unseen=set(range(2*n))
    result=[]
    while unseen:
        stack=[next(iter(unseen))]
        group=set(stack)
        while stack:
            for y in nbr[stack.pop()] - group:
                group.add(y); stack.append(y)
        unseen-=group
        result.append(({a for a in group if a<n},{y-n for y in group if y>=n}))
    return result


def leaves(n, edges, trace):
    matchings=perfect(n,edges)
    assert matchings
    allowed=set().union(*matchings)
    edges={e:ab for e,ab in edges.items() if e in allowed}
    cc=components(n,edges)
    if len(cc)>1:
        trace['products']+=1
        return [item for a,b in cc for item in leaves(len(a),restrict(edges,a,b),trace)]
    if n<=3:
        trace['simplices']+=1
        return [('simplex',set(edges),matchings)]
    A=set(range(n));B=set(range(n))
    for k in range(1,n-1):
        for t in combinations(A,k):
            s=set(t)
            v={b for a,b in edges.values() if a in s}
            assert len(v)>k
            if len(v)!=k+1:
                continue
            trace['cuts']+=1
            li={u:i for i,u in enumerate(sorted(s))};ri={u:i for i,u in enumerate(sorted(v))}
            lo={u:i for i,u in enumerate(sorted(A-s))};ro={u:i for i,u in enumerate(sorted(B-v))}
            g1={e:(li.get(a,k),ri[b]) for e,(a,b) in edges.items() if b in v}
            g2={e:(lo[a],ro.get(b,n-k-1)) for e,(a,b) in edges.items() if a not in s}
            return leaves(k+1,g1,trace)+leaves(n-k,g2,trace)
    trace['braces']+=1
    return [('edge',set(edges),matchings)]


def incidence_vectors(matchings,sets):
    return [sum(1<<i for i,m in enumerate(matchings) if pred(m)) for pred in sets]


def nullspace(columns, n):
    """Integer basis of the orthogonal complement of the columns."""
    rows=[]; piv=[]
    for j in columns:
        row=[Fraction((j>>i)&1) for i in range(n)]
        for p,r in zip(piv,rows):
            if row[p]:
                t=row[p];row=[a-t*b for a,b in zip(row,r)]
        p=next((i for i,x in enumerate(row) if x),None)
        if p is None:
            continue
        z=row[p];row=[a/z for a in row]
        for i,old in enumerate(rows):
            if old[p]:
                t=old[p];rows[i]=[a-t*b for a,b in zip(old,row)]
        where=sum(q<p for q in piv);piv.insert(where,p);rows.insert(where,row)
    out=[]
    for c in sorted(set(range(n))-set(piv)):
        vec=[Fraction(i==c) for i in range(n)]
        for p,r in zip(piv,rows):vec[p]=-r[c]
        scale=lcm(*(q.denominator for q in vec));out.append([int(q*scale) for q in vec])
    return out


def check(n, edges, trace):
    ms=perfect(n,edges)
    if not ms:return
    trace['nonempty_graphs']+=1
    whole=(1<<len(ms))-1
    physical=incidence_vectors(ms,[lambda m,e=e:e in m for e in edges]);physical=list(set(physical))
    orsets={0}
    for v in physical:orsets.update([u|v for u in orsets])
    pure=[u for u in orsets if (whole^u) in orsets]
    trace['pure']+=len(pure)
    features={whole}
    for kind,ids,parts in leaves(n,edges,trace):
        if kind=='edge':
            features.update(incidence_vectors(ms,[lambda m,e=e:e in m for e in ids]))
        else:
            features.update(incidence_vectors(ms,[lambda m,p=p,ids=ids:m&ids==p for p in parts]))
    annihilator=nullspace(features,len(ms))
    for rel in annihilator:
        for u in pure:
            assert sum(x for i,x in enumerate(rel) if (u>>i)&1)==0,(n,edges,u,rel)
    trace['nontrivial_affine_relations']+=len(annihilator)


def canonical_boards(n):
    patterns=range(1<<n)
    maps=[{row:sum(((row>>i)&1)<<p[i] for i in range(n)) for row in patterns} for p in permutations(range(n))]
    for rows in combinations_with_replacement(patterns,n):
        if any(tuple(sorted(col[row] for row in rows))<rows for col in maps):continue
        yield [(a,b) for a,row in enumerate(rows) for b in range(n) if row>>b&1]


def controls():
    tally=defaultdict(int)
    for n in range(1,5):
        cases=0
        for board in canonical_boards(n):
            check(n,dict(enumerate(board)),tally);cases+=1
            if n==3:
                for duplicate in board:
                    check(n,dict(enumerate(board+[duplicate])),tally)
        print(f'n={n}: all {cases} simple row/column-isomorphism classes',flush=True)
    for weights in product(range(3),repeat=4):
        board=[(i//2,i%2) for i,k in enumerate(weights) for _ in range(k)]
        check(2,dict(enumerate(board)),tally)
    for n in (4,5,6):
        for shift in range(2,min(n,4)):
            board=[(i,(i+d)%n) for i in range(n) for d in (0,1,shift)]
            for extras in ([],board[:1],board[:2]):
                check(n,dict(enumerate(board+extras)),tally)
    print('Exact rational lift checks:',dict(sorted(tally.items())),flush=True)


def heawood():
    board={3*i+j:(i,(i+d)%7) for i in range(7) for j,d in enumerate((0,1,3))}
    ms=perfect(7,board);all_edges=frozenset(board);factors=[]
    for i,m in enumerate(ms):
        for j,k in enumerate(ms[:i]):
            if m.isdisjoint(k):
                third=all_edges-(m|k)
                if third in ms[:j]:factors.append((i,j,ms.index(third)))
    assert len(ms)==24 and len(factors)==8
    for i,j,k in factors:
        for x,y in [(i,j),(j,k),(i,k)]:
            assert len(components(7,{e:board[e] for e in ms[x]|ms[y]}))==1
    print('Heawood:',len(ms),'matchings,',len(factors),'rigid unordered factorizations',factors[:2])

if __name__=='__main__':
    heawood();controls()
