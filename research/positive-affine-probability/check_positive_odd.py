"""Exact leading-coefficient checks using the generated physical path data."""
from itertools import product
from positive_odd import hamiltonian,physical,records
from hamiltonian_seed import WeightedGraph


def conditional(route,labels,left,right):
    # Dynamic programming on actual private vertex labels, with fixed endpoint bits.
    # State value is (highest selected reward, number attaining it).
    states={left:(0,1)}
    for v in route[1:-1]:
        w,tag=labels[v]
        assert tag is None
        out={}
        for xt,(score,n) in states.items():
            for nxt in (0,1):
                if xt and nxt:continue
                cand=score+nxt*w
                prev,count=out.get(nxt,(-1,0))
                out[nxt]=(cand,n) if cand>prev else (prev,count+n) if cand==prev else (prev,count)
        states=out
    options=[val for x,val in states.items() if not(x and right)]
    best=max(v for v,c in options)
    return best,sum(c for v,c in options if v==best)


def physical_coefficient(obj,x):
    labels=obj.graph.labels
    n=obj.roots
    if n>21:raise ValueError("fixture too large for physical root enumeration")
    tables=[[conditional(path,labels,a,b) for a,b in product((0,1),repeat=2)] for path in obj.routes]
    total=sum(i for i,_ in labels)
    answer,best=0,-1
    for mask in range(1<<n):
        score=0
        coefficient=1
        for i,(w,tag) in enumerate(labels[:n]):
            if mask>>i&1:score+=w
            elif tag is not None:coefficient*=x[tag]
        for e,(u,v) in enumerate(obj.root_edges):
            q,c=tables[e][2*(mask>>u&1)+(mask>>v&1)]
            score+=q
            coefficient*=c
        if score>best:best=score
        if total-score==obj.leading_exponent:answer+=coefficient
    assert total-best>=obj.leading_exponent
    return answer


def source(n,clauses,x):
    return sum(prod_weights(bits,x) for bits in product((False,True),repeat=n)
        if all(any(bits[abs(lit)-1]==(lit>0) for lit in c) for c in clauses))


def prod_weights(bits,x):
    value=1
    for i,b in enumerate(bits,1):
        if b:value*=x.get(i,1)
    return value


if __name__=='__main__':
    for h in range(3,13):
        private=h+4
        labels=[(0,None)]+[(private+int(i%2==1),None) for i in range(1,2*h+1)]+[(0,None)]
        route=list(range(len(labels)))
        for a,b in product((0,1),repeat=2):
            assert conditional(route,labels,a,b)==(h*(private+1)-h*a-5*a*b,1)
    print("40 exact conditional odd-path maxima and uniqueness controls passed",flush=True)
    # The two unit clauses are the nontrivial monomial x01*x10 of HC2.
    tests=[(1,[],{1:2}),(1,[(1,)],{1:0}),(1,[(-1,)],{1:3}),
           (1,[(1,),(-1,)],{1:1}),(2,[(1,),(2,)],{1:2,2:3}),
           (2,[(1,),(2,)],{1:0,2:3})]
    for n,clauses,x in tests:
        rec,k=records(n,clauses,{i:i for i in x})
        obj=physical(rec,k)
        got=physical_coefficient(obj,x)
        assert got==source(n,clauses,x)
        print(f"n={n} clauses={clauses} physical={len(obj.graph.labels)} leading coefficient={got}",flush=True)
    for n in (2,3,4):
        obj=hamiltonian(n)
        data=[tag for _,tag in obj.graph.labels if tag is not None]
        assert len(data)==len(set(data))==n*n
        print(f"full HC{n} physical={len(obj.graph.labels)} edges={len(obj.graph.edges)} gates={obj.optimum_gates} W={obj.leading_exponent}",flush=True)
