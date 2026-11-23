"""Direct quadratic-extension rank checks for the two nonzero-C parameters."""
from math import comb

P = 65521


class F:
    square = 0

    def __init__(self, x=0, y=0):
        if isinstance(x, F):
            self.a, self.b = x.a, x.b
        else:
            self.a, self.b = x % P, y % P

    def __add__(self, value):
        other = F(value)
        return F(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return F(-self.a, -self.b)

    def __sub__(self, other):
        return self + -F(other)

    def __rsub__(self, other):
        return F(other) - self

    def __mul__(self, value):
        other = F(value)
        return F(self.a * other.a + self.square * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, value):
        other = F(value)
        norm_inv = pow((other.a**2 - self.square*other.b**2) % P, -1, P)
        return self * F(other.a * norm_inv, -other.b * norm_inv)

    def __bool__(self):
        return bool(self.a or self.b)

    def __repr__(self):
        return f'({self.a},{self.b})'


def rref(rows):
    cols = len(rows[0])
    A = [list(map(F, row)) for row in rows]
    pivot = 0
    for j in range(cols):
        k = next((i for i in range(pivot, len(A)) if A[i][j]), None)
        if k is None:
            continue
        A[pivot], A[k] = A[k], A[pivot]
        A[pivot] = [x / A[pivot][j] for x in A[pivot]]
        for i in range(len(A)):
            if i != pivot and A[i][j]:
                c = A[i][j]
                A[i] = [x - c*y for x,y in zip(A[i], A[pivot])]
        pivot += 1
        if pivot == len(A):
            break
    return pivot, A


def moments(a, b, c):
    # Evaluate homogeneous forms at X=1 and several Y, then convert to moments.
    data = {(0,0): F(5), (1,0): F(0), (0,1): F(0)}
    for d in [2,3,4]:
        rows = []
        for y in range(d+1):
            x2, y2, z2 = b*c, a*c*y**2, a*b*(1+y)**2
            xyz = -a*b*c*y*(1+y)
            value = {2:-F(20)/3*(x2+y2+z2), 3:-60*xyz,
                     4:F(260)/9*(x2*x2+y2*y2+z2*z2)-F(200)/9*(x2*y2+x2*z2+y2*z2)}[d]
            rows.append([comb(d,k)*y**k for k in range(d+1)]+[value])
        rank, reduced = rref(rows)
        assert rank == d+1
        for k,row in enumerate(reduced):
            data[d-k,k] = row[-1]
    return data


def check(T, roots):
    a,b,c = roots
    C = F(-2200+39285*T-59049*T*T)/249318
    for root in roots:
        assert not root*root*root - root*root + T*root - C
    assert a-b and b-c and a-c
    m = moments(a,b,c)
    monoms = [(0,0),(1,0),(0,1),(1,1),(0,2)]  # Omit s².
    def product(*terms):
        return tuple(map(sum,zip(*terms)))
    gram = [[m[product(i,j)] for j in monoms] for i in monoms]
    rank, reduced = rref([row+[int(i==j) for j in range(5)] for i,row in enumerate(gram)])
    assert all(not(reduced[i][j]-int(i==j)) for i in range(5) for j in range(5))
    inverse = [row[5:] for row in reduced]
    extra = [m[product(monom,(2,0))] for monom in monoms]
    conic = {(2,0):F(1)}
    for monom,row in zip(monoms,inverse):
        conic[monom] = -sum(x*y for x,y in zip(row,extra))
    equations = []
    def insert(terms):
        line = [F() for _ in range(7)]
        for degree,coefficient in terms:
            if sum(degree)==5:
                line[degree[1]] += coefficient
            else:
                line[-1] -= coefficient*m[degree]
        equations.append(line)
    for j in range(4):
        insert([(product(k,(3-j,j)),v) for k,v in conic.items()])
    for axis in [(1,0),(0,1)]:
        insert([(product(x,y,axis),inverse[j][i]) for i,x in enumerate(monoms)
                for j,y in enumerate(monoms)])
    rank = rref([row[:6] for row in equations])[0]
    augrank = rref(equations)[0]
    print('T',T,'w²',F.square,'roots',roots,'coefficient rank',rank,'augmented rank',augrank)
    assert rank < augrank


if __name__ == '__main__':
    check(45496, list(map(F,(30020,43828,57195))))
    T,r = 57004,4513
    F.square = ((r-1)**2-4*(T+r*(r-1)))%P
    assert pow(F.square,(P-1)//2,P)==P-1
    check(T,[F(r),F(1-r,1)/2,F(1-r,-1)/2])
