"""Check the symmetric six-edge marker and its directed-cycle core gadget."""

from itertools import permutations
from random import Random
from verify_hamiltonian import brute_hc, hc_coefficients, normal


def edge(M,u,v,x):
    assert u != v
    M[u][v] = M[v][u] = x


def case(rng,m,e,p):
    X = [[rng.randint(-5,5) for _ in range(m)] for _ in range(m)]
    core_n = 3*m-1+e
    n = core_n+7
    A = [[0]*n for _ in range(n)]
    D = [[0]*n for _ in range(n)]
    # For each unmarked gadget: in, middle, out. The first one has only in,out.
    a = [0] + [3*i-1 for i in range(1,m)]
    b = [1] + [3*i+1 for i in range(1,m)]
    for i in range(1,m):
        chain = [a[i]]
        if i == 1:
            chain.extend(range(3*m-1,core_n))
        chain.extend((3*i,b[i]))
        for u,v in zip(chain,chain[1:]):
            edge(A,u,v,1)
    for i in range(m):
        for j in range(m):
            if i != j:
                edge(A,b[i],a[j],X[i][j])
    beta,l1,l2,l3,r1,r2,r3 = range(core_n,n)
    for left in ((l1,l2,l3),(r1,r2,r3)):
        cycle = (beta,*left,beta)
        for j,(u,v) in enumerate(zip(cycle,cycle[1:])):
            edge(D,u,v,(-1)**j)
    edge(A,l1,b[0],1)
    edge(A,r1,a[0],1)

    d = [rng.randint(-7,7) for _ in range(n)]
    rows = [rng.randint(-5,5) for _ in range(n)]
    if (sum(rows)-sum(d)) % 2:
        rows[-1] += 1
    for i in range(n):
        A[i][i] = d[i]
    for i in range(core_n):
        edge(A,i,beta,rows[i]-sum(A[i]))
    for i in (l3,r1,r2,r3):
        edge(A,i,beta,rows[i]-sum(A[i]))
    h = {i:rows[i]-sum(A[i]) for i in (beta,l1,l2)}
    for u,v,z in ((beta,l1,l2),(beta,l2,l1),(l1,l2,beta)):
        num = h[u]+h[v]-h[z]
        assert num % 2 == 0
        edge(A,u,v,num//2)
    assert list(map(sum,A)) == rows
    assert not any(map(sum,D)) and not any(D[i][i] for i in range(n))
    assert [A[i][i] for i in range(n)] == d
    assert [i for i in range(core_n) if A[l1][i]] == [b[0]]
    assert [i for i in range(core_n) if A[r1][i]] == [a[0]]
    for j in (l2,l3,r2,r3):
        assert not any(A[j][:core_n])
    out = hc_coefficients(A,D,p,7)
    assert out[6:] == (normal(2*brute_hc(X,p),p),0)
    if p == 2:
        assert not any(out)


def verify_endpoints():
    D = [[0]*7 for _ in range(7)]
    for trip in ((1,2,3),(4,5,6)):
        path = (0,*trip,0)
        for j,(u,v) in enumerate(zip(path,path[1:])):
            edge(D,u,v,(-1)**j)
    paths = {}
    for order in permutations(range(7)):
        if order[0] >= order[-1]:
            continue
        weight = 1
        for u,v in zip(order,order[1:]):
            weight *= D[u][v]
        if weight:
            pair = (order[0],order[-1])
            assert pair not in paths
            paths[pair] = weight
    assert paths == {(1,4):1,(1,6):-1,(3,4):-1,(3,6):1}


if __name__ == '__main__':
    verify_endpoints()
    rng = Random(0xD5C4)
    count = 0
    for p in (0,2,3,5,7):
        for m in (2,3):
            for e in (0,1,2):
                case(rng,m,e,p)
                count += 1
    print(f'Passed {count} symmetric Hamiltonian examples, all three padding classes, through order 17.')
