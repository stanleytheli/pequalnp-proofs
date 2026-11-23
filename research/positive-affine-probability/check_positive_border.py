"""Check the signed-order-free probability estimates, including fixed-zero weights."""
from fractions import Fraction as F
from itertools import product
from random import Random


def check():
    rng=Random(1731)
    N,n=6,4
    total=zeroes=0
    for _ in range(24):
        edges=[(a,b) for a in range(N//2) for b in range(N//2,N) if rng.randrange(3)]
        # b and literal gains sum to at most one. Include identically-zero q_v
        # and coefficients equal to zero, as allowed by the theorem.
        terms=[]
        for _v in range(N):
            weights=[rng.randrange(4) for _ in range(n+1)]
            if rng.randrange(5)==0:weights=[0]*(n+1)
            den=max(1,sum(weights))
            terms.append(([F(x,den) for x in weights],[rng.randrange(2) for _ in range(n)]))
        for x in product((0,1),repeat=n):
            q,d=[],[]
            for vals,sign in terms:
                active=[vals[0]]+[vals[i+1] for i in range(n) if x[i]==sign[i]]
                q.append(sum(active))
                d.append(max(active))
            S,Q=F(0),F(0)
            for mask in range(1<<N):
                if any(not((mask>>u&1) or (mask>>v&1)) for u,v in edges):
                    continue
                score,prob=F(1),F(1)
                for v in range(N):
                    if mask>>v&1:
                        score*=d[v]
                        prob*=q[v]
                    else:
                        prob*=1-q[v]
                S=max(S,score)
                Q+=prob
            assert S/2**N<=Q<=(2*(n+1))**N*S
            assert (Q==0)==(S==0)
            total+=1
            zeroes+=Q==0
    return total,zeroes


if __name__=='__main__':
    total,zeroes=check()
    print(f"{total} exact rational cover/probability inequalities passed, including {zeroes} identically impossible configurations")
