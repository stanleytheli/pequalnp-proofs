"""Original exact coefficient checks for hamiltonian-slices.md; standard library."""

from functools import lru_cache
from itertools import permutations
from math import prod
from random import Random


def normal(x,p):
    return x % p if p else x


def brute_hc(A,p):
    n = len(A)
    return normal(sum(prod(A[u][v] for u,v in zip((0,)+order,order+(0,)))
                      for order in permutations(range(1,n))),p)


def hc_coefficients(A,D,p,degree):
    n = len(A)

    @lru_cache(maxsize=None)
    def paths(end,used):
        if used == (1<<n)-1:
            return (A[end][0],D[end][0]) + (0,)*(degree-1)
        out = [0]*(degree+1)
        for j in range(1,n):
            if used & (1<<j):
                continue
            a,b = A[end][j],D[end][j]
            if not (a or b):
                continue
            rem = paths(j,used|(1<<j))
            for k in range(degree+1):
                out[k] += a*rem[k] + (b*rem[k-1] if k else 0)
        return tuple(normal(x,p) for x in out)

    return paths(0,1)


def case(rng,m,p):
    n = m+4
    X = [[rng.randint(-10,10) for _ in range(m)] for _ in range(m)]
    d = [rng.randint(-6,6) for _ in range(n)]
    rows = [rng.randint(-6,6) for _ in range(n)]
    cols = [rng.randint(-6,6) for _ in range(n-1)]
    cols.append(sum(rows)-sum(cols))
    A = [[0]*n for _ in range(n)]
    oldrows = [4,*range(5,n)]
    oldcols = [0,*range(5,n)]
    for i,u in enumerate(oldrows):
        for j,v in enumerate(oldcols):
            A[u][v] = X[i][j]
    for i in range(n):
        A[i][i] = d[i]
    for i in oldrows:
        A[i][1] += rows[i]-sum(A[i])
    for j in oldcols:
        A[1][j] += cols[j]-sum(row[j] for row in A)

    # Explicit double-star spanning tree. First the three noncentral row leaves,
    # then the three noncentral column leaves; the two central deficits coincide.
    for i in (1,2,3):
        A[i][4] += rows[i]-sum(A[i])
    for j in (1,2,3):
        A[0][j] += cols[j]-sum(row[j] for row in A)
    A[0][4] += rows[0]-sum(A[0])
    assert list(map(sum,A)) == rows and list(map(sum,zip(*A))) == cols
    assert [A[i][i] for i in range(n)] == d

    D = [[0]*n for _ in range(n)]
    for i,j in ((0,1),(1,2),(2,3),(3,4)):
        D[i][j] = 1
    for i,j in ((0,4),(1,3),(3,2),(2,1)):
        D[i][j] = -1
    assert not any(map(sum,D)) and not any(map(sum,zip(*D)))
    assert not any(D[i][i] for i in range(n))
    coeffs = hc_coefficients(A,D,p,5)
    assert coeffs[4:] == (brute_hc(X,p),0)
    # A direct enumeration of unrelated order tests the path recurrence.
    if m <= 3:
        for t in (0,1,-2):
            Y = [[A[i][j]+t*D[i][j] for j in range(n)] for i in range(n)]
            assert brute_hc(Y,p) == normal(sum(c*t**k for k,c in enumerate(coeffs)),p)


if __name__ == '__main__':
    rng = Random(0xDC648)
    count = 0
    for p in (0,2,3,5,7):
        for m in (2,3,4,5):
            for _ in range(4):
                case(rng,m,p)
                count += 1
    print(f'Passed {count} prescribed-diagonal Hamiltonian cycle examples over Z, F2, F3, F5 and F7.')
