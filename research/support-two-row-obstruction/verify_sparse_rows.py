"""Verify the complex seven-plane exclusion for one sparse normal of size 3 or 4.

Every profile, polynomial, degree bound and projection is generated locally.
Requires Python 3.10 or newer and NumPy. Keep Python assertions enabled.
"""

import argparse
from collections import Counter
from functools import reduce
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, gcd
from random import Random

import numpy as np

import verify_full_rows as full



def shapes(u):
    """Enumerate phase configurations under high-row permutations and permutations within each column class."""
    seen = set()
    active = tuple(product((0, 2), repeat=3))
    free = tuple(((*t, -1) for t in product(range(4), repeat=2)))
    for tail in combinations_with_replacement(active, u - 1):
        ac = tuple(sorted(((0, 0, 0), *tail)))
        for un in combinations_with_replacement(free, 5 - u):
            shape = (*ac, *un)
            if shape in seen:
                continue
            orbit = set()
            for perm in permutations(range(3)):
                v = []
                for (h, j, k) in shape:
                    rr = (0, h, j)
                    z = rr[perm[0]]
                    v.append(tuple(((rr[i] - z) % 4 for i in perm[1:])) + ((k - z) % 4 if k != -1 else -1,))
                for first in v[:u]:
                    ww = [tuple(((i - j) % 4 if i != -1 else -1 for (i, j) in zip(c, first))) for c in v]
                    orbit.add((*sorted(ww[:u]), *sorted(ww[u:])))
            seen.update(orbit)
            yield shape


def options(u, shape):
    """List all admissible high-pair orientations and all sparse/full signed or missing-coordinate groups."""
    E = ((0,) * 5, *zip(*shape))
    choices = []
    for i in range(3):
        for k in range(i):
            r = [(a - b) % 4 for (a, b) in zip(E[i], E[k])]
            val = set(r)
            if val == {0, 2}:
                choices.append([('sign', i, k, (), (), 0)])
                continue
            if len(val) != 3:
                return
            z = next((t for t in val if (t + 2) % 4 not in val))
            B = tuple((j for j in range(5) if r[j] == (z + 1) % 4))
            C = tuple((j for j in range(5) if r[j] == (z - 1) % 4))
            choices.append([('three', i, k, B, C, 0), ('three', i, k, C, B, 1)])
    for i in range(3):
        r = [(a - b) % 4 for (a, b) in zip(E[3][:u], E[i][:u])]
        vals = set(r)
        if vals == {0, 2}:
            B = tuple((j for j in range(u) if r[j] == 0))
            C = tuple((j for j in range(u) if r[j] == 2))
            choices.append([('sparse', 3, i, B, C, 0), ('sparse', 3, i, C, B, 1)])
        else:
            assert vals == {0}
            A = []
            for partition in product(range(3), repeat=5 - u):
                if 1 not in partition or 2 not in partition:
                    continue
                B = tuple((j for j in range(u, 5) if partition[j - u] == 1))
                C = tuple((j for j in range(u, 5) if partition[j - u] == 2))
                A.append(('unicolor', 3, i, B, C, 0))
            if not A:
                return
            choices.append(A)
    return (E, choices)


def physical_rows(E, pairs):
    """Build the ten denominator-free covectors on the scaled coordinates."""
    z = full.G
    F = np.zeros((10, 4, 5), dtype=complex)
    V = np.array([[z[a] if a != -1 else 0 for a in row] for row in E])
    for i in range(4):
        F[i, i] = V[i]
    for (f, (tag, i, k, B, C, ori)) in enumerate(pairs, 4):
        if tag == 'sign':
            F[f, i] = -V[k]
            F[f, k] = V[i]
        elif tag == 'three':
            F[f, i, list(B)] = V[i, list(B)]
            F[f, k, list(C)] = V[k, list(C)]
        elif tag == 'sparse':
            F[f, i, list(C)] = V[i, list(C)]
            F[f, k, list(B)] = V[k, list(B)]
        else:
            F[f, i, list(B)] = V[k, list(B)]
            F[f, k, list(C)] = V[k, list(C)]
    return (F.reshape(10, 20), V)


def passes(F):
    """Test every pair projection at the two conjugate split-prime embeddings."""
    p = 1000000009
    root = full.sqrt_i(p)
    a = F.real.astype(np.int64)
    b = F.imag.astype(np.int64)
    rs = []
    cols = [list(range(20))] + [[j for j in range(20) if j // 5 in c] for c in combinations(range(4), 2)]
    fields = ((a + root * b) % p, (a - root * b) % p) if np.any(b) else (a,)
    for J in cols:
        rs.append(max((full.prime_rank((h[:, J] % p).tolist(), p) for h in fields)))
        if len(rs) > 1 and rs[0] - rs[-1] != 3:
            return False
    return True


def check_open(M, forms):
    s = len(M[0][0])
    H = (np.eye(s, dtype=object), np.zeros((s, s), dtype=object))
    for coeff in forms:
        H = full.normalize(full.mul(H, full.add_many([full.scale(a, m) for (a, m) in zip(coeff, M)])))
        if not full.nonzero(H):
            return None
    h = H
    for k in range(s.bit_length()):
        h = full.normalize(full.mul(h, h))
        if not full.nonzero(h):
            return None
    return H


def model(shape, ori, geometry=None):
    """Aggregate columns only when all high phases and sparse-group memberships coincide."""
    shape = tuple(map(tuple, shape))
    assert geometry is not None
    (E, pairs) = geometry
    shape = tuple(((*col, *(int(j in b) + 2 * int(j in c) for (tag, i, k, b, c, o) in pairs if tag == 'unicolor')) for (j, col) in enumerate(shape)))
    unique = tuple(dict.fromkeys(shape))
    indices = [shape.index(q) for q in unique]
    sizes = [shape.count(q) for q in unique]
    (_, V) = physical_rows(E, pairs)
    row = V[:, indices]
    forms = [list(map(full.zz, rr)) for rr in row]
    n = len(unique)
    forms += [[(int(i == j), 0) for j in range(n)] for (i, s) in enumerate(sizes) if s == 1]
    polys = []

    def put(Q):
        out = {}
        for i in range(n):
            for k in range(i, n):
                c = Q[i, k] if i == k else Q[i, k] + Q[k, i]
                if c:
                    t = tuple((int(r == i) + int(r == k) for r in range(n)))
                    out[t] = c
        polys.append(out)
    for (tag, i, k, B, C, ori) in pairs:
        if tag == 'sign':
            forms.extend([list(map(full.zz, row[i] + row[k])), list(map(full.zz, row[i] - row[k]))])
            continue
        b = np.array([int(j in B) for j in indices])
        c = np.array([int(j in C) for j in indices])
        if tag == 'sparse':
            put(np.outer(row[k], row[i] * c) + np.outer(row[i], row[k] * b))
        elif tag == 'unicolor':
            put(np.outer(row[k], row[k] * b) + np.outer(row[i], row[k] * c) - np.outer(row[k], row[i]))
        else:
            a1 = (1 - b - c) * row[k]
            b1 = b * row[k]
            c1 = c * row[k]
            gam = -1j if ori else 1j
            put(np.outer(a1, a1) - np.outer(b1, b1) + np.outer(c1, c1) - 2 * (1 + gam) * np.outer(b1, c1))
    return (shape, unique, sizes, E, pairs, V, forms, polys)


def raw_mac(n, d, polys):
    """Form all degree-d monomial multiples of every homogeneous oriented conic."""
    (es, idx) = full.monomials(n, d)
    xs = full.exponents(d - 2, n)
    m = np.zeros((len(polys) * len(xs), len(es)), dtype=np.complex128)
    for (i, poly) in enumerate(polys):
        for (j, z) in enumerate(xs):
            for (t, c) in poly.items():
                m[i * len(xs) + j, idx[tuple((x + y for (x, y) in zip(t, z)))]] = c
    return (m.real.astype(np.int64), m.imag.astype(np.int64))


def gram(V, pairs, M, p):
    """Evaluate the eleven covectors and their quadratic Gram at block coordinates."""
    d = len(M[0][0])
    r = full.sqrt_i(p)
    w = np.array([np.asarray((a + r * b) % p, dtype=np.int64) for (a, b) in M])
    e = (V.real.astype(np.int64) + r * V.imag.astype(np.int64)) % p
    v = e[:, :, None, None] * w[None, :, :, :] % p
    s = v.sum(1) % p
    F = np.zeros((11, 4, 5, d, d), dtype=np.int64)
    for i in range(4):
        F[i, i] = v[i]
    for (q, (tag, i, k, B, C, ori)) in enumerate(pairs, 4):
        if tag == 'sign':
            for j in range(5):
                F[q, i, j] = -s[k] @ v[k, j] % p
                F[q, k, j] = s[i] @ v[i, j] % p
        elif tag == 'three':
            for j in B:
                F[q, i, j] = s[k] @ v[i, j] % p
            for j in C:
                F[q, k, j] = s[i] @ v[k, j] % p
        elif tag == 'sparse':
            for j in C:
                F[q, i, j] = s[k] @ v[i, j] % p
            for j in B:
                F[q, k, j] = s[i] @ v[k, j] % p
        else:
            for j in B:
                F[q, i, j] = s[k] @ v[k, j] % p
            for j in C:
                F[q, k, j] = s[i] @ v[k, j] % p
    F[10] = np.eye(d, dtype=np.int64)
    F = F.reshape(11, 20, d, d)
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    FD = np.einsum('xy,ayij->axij', K, F) % p
    return np.einsum('axij,bxjk->abik', F, FD) % p


def tangent(shape, unique, sizes, V, pairs, M):
    """Certify nonsingularity of a projected Gram for every allowed duplicate-column split."""
    n = len(unique)
    b = len(M[0][0])
    I = np.eye(b, dtype=object)
    zero = np.zeros((b, b), dtype=object)
    if n == 4:
        v = unique[sizes.index(2)]
        assert sizes.count(2) == 1

    def values(t):
        out = []
        matched = False
        for col in shape:
            i = unique.index(col)
            u = M[i]
            if n == 5:
                out.append(u)
                continue
            if col == v:
                out.append(full.add_many([u, ((-t if matched else t) * I, zero)]))
                matched = True
            else:
                out.append(full.scale((2, 0), u))
        return out
    for p in (65521, 1009, 241):
        G = gram(V, pairs, values(0), p)
        if n == 4:
            inc = (gram(V, pairs, values(1), p) - G) % p
            assert np.array_equal((G + 4 * inc) % p, gram(V, pairs, values(2), p))
        common = []
        full_deg = False
        for seed in range(18):
            rr = Random(seed)
            A = np.array([[rr.randrange(-7, 8) for j in range(11)] for i in range(7)], np.int64)
            B = np.einsum('ia,abuv,jb->iujv', A, G, A).reshape(7 * b, 7 * b) % p
            if n == 5:
                if full.full_rank(B, p):
                    return (p, seed)
            else:
                C = np.einsum('ia,abuv,jb->iujv', A, inc, A).reshape(7 * b, 7 * b) % p
                cols = [j for j in range(5) if shape[j] == v]
                low_absent = not np.any(V[3, cols]) and all((not any((j in B for j in cols)) for (tag, i, k, B, C, ori) in pairs if tag == 'unicolor'))
                deg = (2 if low_absent else 4) * b
                vs = [full.determinant((B + j * C) % p, p) for j in range(deg + 1)]
                pol = full.interpolate(vs, p)
                if len(pol) == deg + 1:
                    full_deg = True
                if pol:
                    common = full.poly_gcd(common, pol, p)
                if full_deg and common == [1]:
                    return (p, seed)


def check(shape, ori, geometry=None):
    """Recover the finite dual and rule out nonzero evaluations on the required open set."""
    (shape, unique, sizes, E, pairs, V, forms, polys) = model(shape, ori, geometry)
    n = len(unique)
    d = n + 1
    if len(polys) < n - 1:
        return ('curve', 0)
    (A, B) = raw_mac(n, d, polys)
    res = full.lift(A, B, full.EXTENDED)
    if res is None:
        return ('lift', -1)
    E = res[0]
    while E and d >= 2:
        (M, _) = full.multiplication(E, n, d)
        if M is not None:
            H = check_open(M, forms)
            if H is None:
                return ('excluded', len(E))
            N = full.compressed(M, H)
            if not N:
                return ('compression', -1)
            ok = tangent(shape, unique, sizes, V, pairs, N)
            return ('tangent' if ok else 'unresolved', len(N[0][0]))
        (E, _) = full.shrink(E, n, d, forms)
        d -= 1
        if E is None:
            return ('compression', -1)
    return ('excluded' if not E else 'positive', len(E))


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def primitive(f):
    """Make a canonical primitive integer polynomial, coefficients in increasing degree."""
    f = trim(f)
    if not f:
        return []
    c = reduce(gcd, f, 0)
    s = c if f[-1] > 0 else -c
    return [x // s for x in f]


def multiply(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for (j, y) in enumerate(g):
        for (i, x) in enumerate(f):
            r[i + j] += x * y
    return trim(r)


def gcdq(f, g):
    """Compute the monic-up-to-integer-content gcd in the rational univariate polynomial ring."""
    f = primitive(f)
    g = primitive(g)
    while g:
        while len(f) >= len(g):
            a = f[-1]
            b = g[-1]
            c = gcd(a, b)
            a //= c
            b //= c
            diff = len(f) - len(g)
            f = primitive([b * x - (a * g[i - diff] if i >= diff else 0) for (i, x) in enumerate(f)])
        (f, g) = (g, f)
    return f


def quotient(f, g):
    out = [0] * (len(f) - len(g) + 1)
    f = f.copy()
    while len(f) >= len(g):
        z = len(f) - len(g)
        (k, r) = divmod(f[-1], g[-1])
        assert r == 0
        out[z] = k
        f = trim([v - (k * g[i - z] if i >= z else 0) for (i, v) in enumerate(f)])
    assert not f
    return primitive(out)


def remove(f, forms):
    f = primitive(f)
    if not f:
        return []
    for q in forms:
        while len(f) > 1:
            h = gcdq(f, q)
            if len(h) <= 1:
                break
            f = quotient(f, h)
    return f


def idet(a):
    A = [r.copy() for r in a]
    n = len(A)
    old = 1
    s = 1
    for i in range(n - 1):
        k = next((j for j in range(i, n) if A[j][i]), None)
        if k is None:
            return 0
        if k != i:
            (A[k], A[i]) = (A[i], A[k])
            s = -s
        pivot = A[i][i]
        for j in range(i + 1, n):
            v = A[j][i]
            for h in range(i + 1, n):
                A[j][h] = (pivot * A[j][h] - v * A[i][h]) // old
        old = pivot
    return s * A[-1][-1]


def inter(y):
    """Recover an integer polynomial up to nonzero constant by univariate Newton differences."""
    n = len(y)
    pol = [0] * n
    fall = [1]
    fac = 1
    for j in range(n):
        (q, r) = divmod(y[0], fac)
        assert r == 0
        for (k, c) in enumerate(fall):
            pol[k] += q * c
        y = [b - a for (a, b) in zip(y, y[1:])]
        fac *= j + 1
        fall = multiply(fall, [-j, 1])
    return primitive(pol)


def reparam(V, pairs, branch):
    """Use one of the two roots shared by all three high rows as the parameter at support four."""
    V = V.real.astype(int)
    T = V[:, :4]
    R = T.tolist()
    d = full.det(R)
    adj = np.array([[(-1) ** (i + j) * full.det([[R[a][b] for b in range(4) if b != i] for a in range(4) if a != j]) for j in range(4)] for i in range(4)])
    assert d and np.array_equal(adj @ T, d * np.eye(4, dtype=int))
    out = np.zeros((4, 3), dtype=int)
    out[3, 1] = 1
    for (tag, i, k, B, C, o) in pairs:
        if tag != 'sparse':
            continue
        h = int(V[3, B[0]] * V[k, B[0]])
        epsilon = int(V[k, 4])
        out[k, 1] = h
        if k == 0 or not branch >> k - 1 & 1:
            out[k, 2] = epsilon
        else:
            out[k, 0] = -2 * epsilon
    A = np.vstack([adj @ out, d * np.array([2, 0, -1])])
    s = V @ A
    forms = [*A, *s]
    for (tag, i, k, B, C, o) in pairs:
        if tag == 'sign':
            forms.extend((s[i] + s[k], s[i] - s[k]))
    return (A, [primitive([int(c) for c in u]) for u in forms])


def plus(a, b):
    return trim([(a[k] if k < len(a) else 0) + (b[k] if k < len(b) else 0) for k in range(max(len(a), len(b)))])


def divexact(a, b):
    if not a:
        return []
    q = [0] * (len(a) - len(b) + 1)
    a = a.copy()
    while len(a) >= len(b):
        j = len(a) - len(b)
        (v, r) = divmod(a[-1], b[-1])
        assert r == 0
        q[j] = v
        a = plus(a, [0] * j + [-v * y for y in b])
    assert not a
    return q


class Rat:

    def __init__(self, n, d=1):
        if isinstance(n, Rat):
            (self.n, self.d) = (n.n, n.d)
            return
        n = [int(n)] if isinstance(n, (int, np.integer)) else list(n)
        d = [int(d)] if isinstance(d, (int, np.integer)) else list(d)
        n = trim(n)
        d = trim(d)
        assert d
        g = gcdq(n, d)
        if len(g) > 1:
            n = divexact(n, g)
            d = divexact(d, g)
        g = reduce(gcd, (*n, *d), 0) * (1 if d[-1] > 0 else -1)
        self.n = [v // g for v in n]
        self.d = [v // g for v in d]

    def __add__(self, o):
        o = Rat(o)
        return Rat(plus(multiply(self.n, o.d), multiply(self.d, o.n)), multiply(self.d, o.d))
    __radd__ = __add__

    def __neg__(self):
        return Rat([-x for x in self.n], self.d)

    def __sub__(self, o):
        return self + -Rat(o)

    def __rsub__(self, o):
        return Rat(o) + -self

    def __mul__(self, o):
        o = Rat(o)
        return Rat(multiply(self.n, o.n), multiply(self.d, o.d))
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = Rat(o)
        return Rat(multiply(self.n, o.d), multiply(self.d, o.n))

    def __rtruediv__(self, o):
        return Rat(o) / self

    def __eq__(self, o):
        return not (self - o).n


def mass_curves(V, pp):
    """Parametrize every sign-compatible possibility at support three, including repeated-root cases."""
    V = V.real.astype(int)
    R = V[:, :3].tolist()
    dep = [(-1) ** i * full.det([r for (j, r) in enumerate(R) if j != i]) for i in range(4)]
    rp = next((k for k in range(4) if dep[k]))
    rows = [j for j in range(4) if j != rp]
    T = [R[i] for i in rows]
    det = full.det(T)
    adj = [[(-1) ** (i + j) * full.det([[T[a][b] for b in range(3) if b != i] for a in range(3) if a != j]) for j in range(3)] for i in range(3)]
    assert np.array_equal(np.array(adj) @ np.array(T), det * np.eye(3, dtype=int))
    kv = [v for v in pp if v[0] == 'unicolor']
    hs = {k: int(V[3, B[0]] * V[k, B[0]]) for (tag, i, k, B, C, o) in pp if tag == 'sparse'}
    v = Rat([0, 1])
    charts = []
    if kv:
        assert len(kv) == 1
        (_, _, g, ppp, qqq, _) = kv[0]
        (j,) = ppp
        (l,) = qqq
        eb = int(V[g, j])
        ec = int(V[g, l])
        prop = {k: int(V[k, j]) * eb for k in hs}
        modes = {k: prop[k] * int(V[k, l]) * ec for k in hs}
        direct = [k for k in hs if modes[k] == 1]
        t = v / (2 - v * v) if direct else v
        for signs in product((0, 1), repeat=len(hs)):
            if direct and signs[list(hs).index(direct[0])]:
                continue
            uu = [Rat(0), Rat(0), Rat(0), Rat(1)]
            uu[g] = Rat(1)
            for (flag, k) in zip(signs, hs):
                if modes[k] == 1:
                    z = v if not flag else -2 / v
                else:
                    z = 1 / t if not flag else -2 * t
                uu[k] = hs[k] + prop[k] * z
            tt = {j: eb * t, l: ec * (1 / t - t)}
            charts.append((uu, tt[3], tt[4]))
    else:
        modes = [int(V[k, 3] * V[k, 4]) for k in range(3)]
        same = next((m for m in set(modes) if modes.count(m) == 2))
        both = [k for k in range(3) if modes[k] == same]
        last = next((k for k in range(3) if modes[k] != same))
        assert dep[last]
        for flag in (0, 1):
            uu = [Rat(0), Rat(0), Rat(0), Rat(1)]
            for (h, k) in enumerate(both):
                uu[k] = hs[k] + int(V[k, 3]) * (v if not (h and flag) else -2 / v)
            uu[last] = -sum((dep[j] * uu[j] for j in range(4) if j != last)) / dep[last]
            w = (uu[last] - hs[last]) * int(V[last, 3])
            if not w.n:
                continue
            pair = {same: 2 / v - v, -same: 2 / w - w}
            charts.append((uu, (pair[1] + pair[-1]) / 2, (pair[1] - pair[-1]) / 2))
    for (uu, p, q) in charts:
        assert sum((dep[j] * uu[j] for j in range(4))) == 0
        ws = [sum((u * uu[k] for (u, k) in zip(a, rows))) / det for a in adj] + [p, q]
        for (tag, i, k, B, C, o) in pp:
            if tag == 'sign':
                continue
            sk = sum((int(V[k, j]) * ws[j] for j in range(5)))
            sw = sum((int(V[3, j]) * ws[j] for j in range(5)))
            if tag == 'sparse':
                val = sk * sum((int(V[3, j]) * ws[j] for j in C)) + sw * sum((int(V[k, j]) * ws[j] for j in B))
            else:
                val = sk * sum((int(V[k, j]) * ws[j] for j in B)) + sw * sum((int(V[k, j]) * ws[j] for j in C)) - sk * sw
            assert val == 0
        den = reduce(multiply, (w.d for w in ws), [1])
        nums = [multiply(w.n, divexact(den, w.d)) for w in ws]
        g = reduce(gcdq, nums)
        nums = [divexact(s, g) for s in nums]
        f = reduce(gcd, (y for x in nums for y in x), 0)
        nums = [[v // f for v in x] for x in nums]
        Z = max(map(len, nums))
        M = np.array([w + [0] * (Z - len(w)) for w in nums], dtype=object)
        yield M


def minors(V, pairs, A):
    """Remove exactly dividing forbidden factors and test the gcd of integer projected Gram minors."""
    V = V.real.astype(int)
    s = V @ A
    forms = [*A, *s]
    for (tag, i, k, B, C, o) in pairs:
        if tag == 'sign':
            forms.extend((s[i] + s[k], s[i] - s[k]))
    forms = [primitive([int(x) for x in u]) for u in forms]
    if any((not f for f in forms)):
        return ('boundary', 0)
    KL = np.kron(3 * np.eye(4, dtype=int) - 1, 4 * np.eye(5, dtype=int) - 1).astype(object)
    profile = ((1, 4, 2), (1, 3, 3), (0, 4, 3), (0, 3, 4), (1, 2, 4), (1, 1, 5))
    m = A.shape[1] - 1

    def g(t):
        w = A @ np.array([t ** i for i in range(m + 1)], dtype=object)
        v = V * w[None, :]
        s = v.sum(1)
        F = np.zeros((11, 4, 5), dtype=object)
        for i in range(4):
            F[i, i] = v[i]
        for (r, (tag, i, k, B, C, o)) in enumerate(pairs, 4):
            if tag == 'sign':
                F[r, i] = -s[k] * v[k]
                F[r, k] = s[i] * v[i]
            elif tag == 'sparse':
                F[r, i, list(C)] = s[k] * v[i, list(C)]
                F[r, k, list(B)] = s[i] * v[k, list(B)]
            else:
                F[r, i, list(B)] = s[k] * v[k, list(B)]
                F[r, k, list(C)] = s[i] * v[k, list(C)]
        F[10] = 1
        X = F.reshape(11, 20)
        return X @ KL @ X.T
    gs = []
    common = []
    for seed in range(3 * len(profile)):
        (n0, n1, n2) = profile[seed % len(profile)]
        deg = 2 * m * (n1 + 2 * n2)
        gs.extend((g(t) for t in range(len(gs), deg + 1)))
        rng = Random(seed + 103)
        P = np.zeros((7, 11), dtype=object)
        if n0:
            P[0, 10] = 1
        P[n0:n0 + n1, :4] = [[rng.randrange(-7, 8) for j in range(4)] for i in range(n1)]
        P[n0 + n1:, 4:10] = [[rng.randrange(-7, 8) for j in range(6)] for i in range(n2)]
        q = inter([idet((P @ G @ P.T).tolist()) for G in gs[:deg + 1]])
        q = remove(q, forms)
        if q:
            common = gcdq(common, q)
        if common == [1]:
            return ('excluded', seed + 1)
    return ('residual', common)



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support', type=int, choices=(3,4))
    parser.add_argument('--part', choices=('all','profiles','finite','curves'), default='all')
    parser.add_argument('--shard', nargs=2, type=int, metavar=('INDEX','COUNT'), default=(0,1))
    args = parser.parse_args()
    index, shards = args.shard
    assert 0 <= index < shards
    for support in ([args.support] if args.support else [3,4]):
        accepted = 0
        finite = Counter()
        curve = Counter()
        curves = 0
        for shape in shapes(support):
            val = options(support,shape)
            if val is None:
                continue
            E,choices = val
            for pairs in product(*choices):
                F,V = physical_rows(E,pairs)
                if not passes(F):
                    continue
                serial = accepted
                accepted += 1
                if args.part == 'profiles' or serial % shards != index:
                    continue
                geometry = E,pairs
                _,unique,_,_,_,_,_,polys = model(shape,0,geometry)
                if len(polys) >= len(unique)-1:
                    if args.part in ('all','finite'):
                        status,dimensions = check(shape,0,geometry)
                        assert status in ('excluded','tangent'), (shape,pairs,status,dimensions)
                        finite[status] += 1
                    continue
                curves += 1
                if args.part not in ('all','curves'):
                    continue
                assert len(unique)==5 and all(t!='three' for t,*_ in pairs)
                if support == 4:
                    charts = (reparam(V,pairs,b)[0] for b in range(4))
                else:
                    charts = mass_curves(V,pairs)
                for masses in charts:
                    status,details = minors(V,pairs,masses.astype(object))
                    assert status in ('boundary','excluded'), (shape,pairs,status,details)
                    curve[status] += 1
        assert accepted == {3:1407,4:713}[support]
        if shards == 1:
            if args.part in ('all','finite'):
                assert finite == {3:{'excluded':1359,'tangent':6},4:{'excluded':635,'tangent':6}}[support]
            if args.part in ('all','curves'):
                assert curves == {3:42,4:72}[support]
                assert curve == {3:{'boundary':55,'excluded':59},4:{'boundary':180,'excluded':108}}[support]
        print('Support',support,'retained orientations',accepted,'finite',dict(finite),
              'parameterized branches',dict(curve),flush=True)

if __name__ == '__main__':
    main()
