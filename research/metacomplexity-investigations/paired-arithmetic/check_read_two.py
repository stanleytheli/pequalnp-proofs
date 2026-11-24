from itertools import product
from random import Random
from read_two_floor import closed


def test(clauses, n):
    mask=(1<<n)-1
    models={a for a in range(1<<n) if all(any(bool(a & (1<<(abs(l)-1))) == (l>0) for l in c) for c in clauses)}
    count=0
    for base in models:
        normalized={a^base for a in models}
        expected=(all(mask^a in normalized for a in normalized) and
                  all(a&b in normalized for a in normalized for b in normalized))
        verdict=closed(clauses,n,[bool(base & (1<<i)) for i in range(n)])
        assert verdict==expected,(clauses,n,base)
        count+=1
    return count


if __name__=='__main__':
    rng=Random(94781)
    cases=0
    for n in range(1,9):
        for _ in range(70):
            pool=list(range(1,n+1))*2
            rng.shuffle(pool)
            clauses=[]
            while pool:
                width=rng.randint(1,min(7,len(pool)))
                clauses.append([pool.pop()*rng.choice((-1,1)) for _ in range(width)])
            cases+=test(clauses,n)
    # Include genuinely complementary, non-product and duplicate-literal cases.
    for clauses,n in [([(-1,2),(1,-2)],2),([(-1,-2,-3)],3),([],4),([(1,-1,2),(3,-3)],3)]:
        cases+=test(clauses,n)
    print(f"read-two arbitrary-width closure matched full truth tables at {cases} satisfying baselines")
