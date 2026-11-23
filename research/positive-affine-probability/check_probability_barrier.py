"""Exhaust cut complements and their single-arc repairs for orders up to seven."""
from itertools import permutations
from fractions import Fraction
from random import Random


def arcs(tour):
    return set(zip(tour,tour[1:]+tour[:1]))


def check_cuts(m):
    all_arcs={(i,j) for i in range(m) for j in range(m)}
    cycles=[arcs((0,)+p) for p in permutations(range(1,m))]
    rejected=[]
    repaired=0
    for mask in range(1,2**m-1):
        bad=frozenset((u,v) for u in range(m) for v in range(m) if mask>>u&1 and not mask>>v&1)
        assert bad and all(t&bad for t in cycles)
        for missing in bad:
            assert any(t&bad=={missing} for t in cycles)
            repaired+=1
        rejected.append(bad)
    assert len(set(rejected))==2**m-2
    assert all(not (i<=j or j<=i) for ix,i in enumerate(rejected) for j in rejected[ix+1:])
    assert max(map(len,rejected))==m*m//4
    return len(rejected),repaired


def check_probabilities():
    rng=Random(20261123)
    n=5
    vertices=range(6)
    pairs=[(0,1),(1,3),(2,4),(2,5),(3,4)]
    for _ in range(40):
        coeff=[[rng.randrange(-2,3) for _ in range(n)] for _ in vertices]
        denominators=[max(1,sum(abs(x) for x in row)) for row in coeff]
        for x in range(2**n):
            p=[]
            for row,d in zip(coeff,denominators):
                shift=-sum(min(0,w) for w in row)
                p.append(Fraction(shift+sum(w for i,w in enumerate(row) if x>>i&1),d))
            probability=0
            for selected in range(2**len(vertices)):
                if any(selected>>a&1 and selected>>b&1 for a,b in pairs):
                    continue
                weight=1
                for v in vertices:
                    weight*=p[v] if selected>>v&1 else 1-p[v]
                probability+=weight
            assert (probability>0)==all(p[a]!=1 or p[b]!=1 for a,b in pairs)
            assert (probability<1)==any(p[a]>0 and p[b]>0 for a,b in pairs)
    return 40*2**n


if __name__=='__main__':
    for m in range(2,8):
        cuts,repairs=check_cuts(m)
        print(f"m={m} maximal cuts={cuts} repairs={repairs}",flush=True)
    print(f"{check_probabilities()} exact affine probability controls passed")
