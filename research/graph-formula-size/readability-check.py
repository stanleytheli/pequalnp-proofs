from itertools import combinations,product
from random import Random
from readability import star_orientation,formula_occurrences,readability

def exhaustive(n,edges,bounds):
    for orientation in product((0,1),repeat=len(edges)):
        owner=[e[bit] for e,bit in zip(edges,orientation)]
        _,count=formula_occurrences(n,edges,owner)
        if all(a<=b for a,b in zip(count,bounds)):return True
    return False
rng=Random(294025)
checks=0
for n in range(2,6):
    pairs=list(combinations(range(n),2))
    for mask in range(1,1<<len(pairs)):
        edges=[e for i,e in enumerate(pairs) if mask>>i&1]
        for _ in range(4):
            bound=[rng.randrange(n) for i in range(n)]
            try:owner,cut=star_orientation(n,edges,bound)
            except ValueError:break
            assert (owner is not None)==exhaustive(n,edges,bound)
            if owner is not None:
                groups,count=formula_occurrences(n,edges,owner)
                assert all(a<=b for a,b in zip(count,bound))
                for x in range(1<<n):
                    assert any(x>>v&1 and any(x>>w&1 for w in group) for v,group in enumerate(groups))==any(x>>u&x>>v&1 for u,v in edges)
            checks+=1
print('Compared',checks,'feasibility decisions with exhaustive orientation search.')
sets=list(combinations(range(5),2))
petersen=[(i,j) for i,j in combinations(range(10),2) if set(sets[i]).isdisjoint(sets[j])]
from plane import edges as plane_edges
heawood=[(p,7+j) for p,row in enumerate(((0,1,3),(0,2,6),(1,5,6),(0,4,5),(3,4,6),(2,3,5),(1,2,4))) for j in row]
for name,n,edges in [('Petersen',10,petersen),('Heawood',14,heawood),('order-three plane',26,plane_edges)]:
    k,groups=readability(n,edges)
    assert k==3
    print(name,'readability',k,'orientation',[(v,sorted(g)) for v,g in enumerate(groups) if g])
