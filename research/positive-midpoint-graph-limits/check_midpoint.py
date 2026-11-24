"""Exhaustive small midpoint limits versus their shared CNFs, plus independent HC and parity checks."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import prod
from random import Random


def vertices(mask,n):
    return [i for i in range(n) if mask>>i&1]


def clauses_for_slice(n,good):
    assert good
    # A bank entry is a set of one or two vertex forms whose disjunction is required.
    single=[(v,) for v in range(n) if all(c>>v&1 for c in good)]
    pairs=[(v,w) for v,w in combinations(range(n),2) if all(c>>v&1 or c>>w&1 for c in good)]
    return set(single+pairs)


def check_limit(n,edges,T,degree,lits):
    covers=[c for c in range(1<<n) if all((c>>u|c>>v)&1 for u,v in edges)]
    cost=lambda c: sum(degree[v] for v in vertices(c,n))
    tau=min(map(cost,covers))
    good=[c for c in covers if cost(c)==tau]
    groups=defaultdict(list)
    for c in good: groups[c&T].append(c)
    branches=[clauses_for_slice(n,a) for a in groups.values()]
    # A cover-absent event is feasible exactly when the required vertices can all be absent.
    # Enumerate every possible mask independently of the optional actual literal map below.
    for enabled in range(1<<n):
        actual=any(not c&~enabled for c in good)
        cnf=any(all(any(enabled>>v&1 for v in clause) for clause in cols) for cols in branches)
        assert actual==cnf
    # Also calculate the coefficient of t^tau directly from the product Bernoulli law,
    # including zero exponent vertices where the occupied-state factor is 1-d rather than 1.
    nbits=max([abs(j) for xs in lits for j in xs]+[1])
    for raw in range(1<<nbits):
        def bit(j): return int(bool(raw>>(abs(j)-1)&1)==(j>0))
        d=[sum(bit(j) for j in xs)/Fraction(len(xs)) for xs in lits]
        coeff=Fraction(0)
        for S in range(1<<n):
            if any(S>>u&1 and S>>v&1 for u,v in edges): continue
            c=((1<<n)-1)^S
            if cost(c)!=tau: continue
            coeff+=prod(d[v] for v in vertices(c,n))*prod(1-d[v] for v in vertices(S,n) if degree[v]==0)
        cnf=any(all(any(d[v]>0 for v in col) for col in cols) for cols in branches)
        assert (coeff>0)==cnf
    return len(branches)


def ham_exists(m,edges):
    # Held–Karp with a fixed start, allowing no repeated vertex.
    paths={1:1}
    for S in range(1,1<<m,2):
        last=paths.get(S,0)
        for v in vertices(last,m):
            for w in range(1,m):
                if not S>>w&1 and (v,w) in edges:
                    new=S|1<<w
                    paths[new]=paths.get(new,0)|1<<w
    return any((v,0) in edges for v in vertices(paths.get((1<<m)-1,0),m))


def maximal_obstructions(m,r):
    sep=set(range(r-1));leaders=list(range(r-1,2*r-1));followers=list(range(2*r-1,m))
    full=set(product(range(m),repeat=2)); checked=0
    for owners in product(leaders,repeat=len(followers)):
        tag=dict(zip(followers,owners))|{i:i for i in leaders}
        E={(i,j) for i,j in full if i in sep or j in sep or tag[i]==tag[j]}
        assert not ham_exists(m,E)
        for extra in full-E:
            assert ham_exists(m,E|{extra})
            checked+=1
    return r**len(followers),checked


def popcount(n):
    return bin(n).count("1")


def parity_halves(n):
    left=n//2; right=n-left
    for x in range(1<<n):
        a=x%(1<<left); b=x>>left
        ql=[popcount(i^a)/Fraction(left) for i in range(1<<left)]
        qr=[popcount(j^b)/Fraction(right) for j in range(1<<right)]
        bad=any(ql[i]==qr[j]==0 and (popcount(i)+popcount(j))%2==0
                for i in range(len(ql)) for j in range(len(qr)))
        assert (not bad)==bool(popcount(x)%2)


def run():
    rng=Random(2401)
    pair_count=0
    for s in range(140):
        n=4 if s<16 else 6
        half=n//2; edges=[]
        for i,j in combinations(range(n),2):
            if (i<half<=j or (s%2 and i==0)) and rng.randrange(3): edges.append((i,j))
        T=1 if s%2 else 0
        degree=[rng.randrange(4) for _ in range(n)]
        lits=[[rng.choice([-1,1])*rng.randint(1,4) for _ in range(rng.randrange(1,4))] for v in range(n)]
        pair_count+=check_limit(n,edges,T,degree,lits)
    print(f'140 weighted graphs, {pair_count} nonempty optimal-cover slices; all admissibility masks and assigned corners checked')
    count=arcs=0
    for m,r in [(4,2),(5,2),(6,2),(6,3),(7,2),(7,3),(8,3)]:
        a,b=maximal_obstructions(m,r);count+=a;arcs+=b
    print(f'{count} non-Hamiltonian separator matrices and all {arcs} one-arc Hamiltonian extensions verified by Held–Karp')
    for n in range(2,11): parity_halves(n)
    print('bipartite half-record parity representations checked on all inputs at n=2,…,10')

if __name__=='__main__': run()
