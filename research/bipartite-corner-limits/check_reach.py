"""Independent exhaustive matching, edge-event, and CNF lower controls."""
from itertools import combinations, product
from random import Random
from reach_border import active, construct, diamonds, matching, reachable


def cover_min(g,bits):
    verts=[i for i,lab in enumerate(g.labels) if active(lab,bits)]
    edges=[(u,v) for u,v in g.edges if u in verts and v in verts]
    for k in range(len(verts)+1):
        count=0
        for subset in combinations(verts,k):
            S=set(subset)
            count+=all(u in S or v in S for u,v in edges)
        if count:
            return k,count


def check():
    rng=Random(3571)
    tests=raw=0
    for n in range(2,8):
        for t in range(6):
            nbits=3
            opts=[None,0,1,-1,2,-2,3,-3]
            arcs=[(i,j,rng.choice(opts)) for i in range(n) for j in range(n) if i!=j and rng.randrange(4)==0]
            g,b=construct(n,arcs)
            for bits in product((False,True),repeat=nbits):
                m=matching(g,bits)
                assert m==b+int(reachable(n,arcs,bits))
                if len(g.labels)<15:
                    k,count=cover_min(g,bits)
                    assert k==m and count>=1
                    raw+=1
                tests+=1
    separated=0
    for k in range(1,7):
        n,arcs=diamonds(k)
        g,b=construct(n,arcs)
        assert b==3*k-1
        degree=[0]*len(g.labels)
        for u,v in g.edges:
            degree[u]+=1;degree[v]+=1
        assert max(degree)<=3
        for bits in product((False,True),repeat=2*k):
            d=any(not bits[2*i] and not bits[2*i+1] for i in range(k))
            assert (matching(g,bits)==b)==d
            tests+=1
        zeros=[tuple(v for p in choices for v in (p,not p)) for choices in product((False,True),repeat=k)]
        for a,c in combinations(zeros,2):
            z=[x and y for x,y in zip(a,c)]
            assert any(not z[2*i] and not z[2*i+1] for i in range(k))
            separated+=1
    print(f"{tests} matching/Boolean-limit controls, {raw} direct minimum-cover enumerations, "
          f"and {separated} separated clause pairs passed")


if __name__=='__main__':
    check()
