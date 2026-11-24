"""Compare compiled independent Boolean corners with direct gate and witness evaluation."""
from itertools import product
from random import Random
from closure import construct, evaluate, optimum, stretch


def validate(g, data, t):
    incidences=[0]*len(g.costs)
    E=g.edges+g.special
    assert len({tuple(sorted(e)) for e in E})==len(E)
    for u,v in E:
        assert u!=v
        incidences[u]+=1;incidences[v]+=1
    assert min(incidences)>0 and max(incidences)<=3 and len(g.special)==t
    for i in range(data):
        assert sum(c.index==i for c in g.costs)==2


def check():
    rng=Random(30019)
    base=paths=rows=0
    # Conditional gate optima by exhaustive row/rail search on a fully pinned input.
    for truth in range(16):
        for i,j in product((0,1),repeat=2):
            costs=[]
            for row in product((0,1),repeat=4):
                if any(v for q,v in enumerate(row) if q!=2*i+j):
                    continue
                for output in product((0,1),repeat=2):
                    if any(v and not output[(truth>>q)&1] for q,v in enumerate(row)):
                        continue
                    costs.append((2*(4-sum(row))+sum(output),row,output))
            cs=sorted(costs)
            assert cs[0][0]==7 and cs[1][0]>=8
            assert cs[0][2][(truth>>(2*i+j))&1]
            rows+=1
    cases=[(1,0,[]),(1,1,[]),(2,1,[(0,2,8),(1,3,6)]),(1,2,[(0,1,5),(2,3,4)])]
    cases += [(2,0,[(0,1,t)]) for t in range(16)]
    for _ in range(6):
        n,t=2,rng.randrange(3)
        gates=[]
        for j in range(3):
            gates.append((rng.randrange(n+t+j),rng.randrange(n+t+j),rng.randrange(16)))
        cases.append((n,t,gates))
    for i,(n,t,gates) in enumerate(cases):
        g=construct(n,t,gates)
        validate(g,n,t)
        p=stretch(g) if i<4 or i in (5,9,14,21,23) else None
        if p:
            validate(p,n,t)
            assert len(p.stars)==len(g.costs)+4*len(g.edges)+5*len(g.special)
            star_edges={tuple(sorted((c,j))) for c,ns in p.stars.items() for j in ns}
            assert star_edges=={tuple(sorted(e)) for e in p.edges+p.special}
            reads=[0]*len(p.costs)
            for c,ns in p.stars.items():
                reads[c]+=1
                for u in ns:
                    reads[u]+=1
            assert min(reads)==1 and max(reads)<=2
        for bits in product((0,1),repeat=n):
            witnesses=sum(evaluate(bits+w,gates) for w in product((0,1),repeat=t))
            accepted=witnesses>0
            value,count=optimum(g,bits,True)
            assert value==g.base+int(not accepted),(i,bits)
            assert count==witnesses if accepted else count>=1
            base+=1
            if p:
                value,count=optimum(p,bits,True)
                assert value==p.base+int(not accepted),(i,bits)
                assert count==witnesses if accepted else count>=1
                paths+=1
    print(f"{rows} exhaustive row-state controls, {base} physical core min-cuts, "
          f"and {paths} full mixed long-subdivision cover optimizations with exact minimizing multiplicities and read-two star partitions passed")


if __name__=='__main__':
    check()
