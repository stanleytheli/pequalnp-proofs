"""Verify the disjoint support-two mixed-row restriction."""
import argparse
from collections import Counter
from itertools import combinations,product
from functools import reduce
from fractions import Fraction
from math import lcm,factorial
from random import Random
import numpy as np
import verify_full_rows as full
import verify_mixed_rows as mixed
import verify_sparse_rows as sparse
import verify_support_two as tower
import verify_mixed_two as mx
from verify_mixed_rows import geom,constraints,gram
from verify_sparse_rows import raw_mac,idet,inter,remove,primitive,plus
from verify_support_two import gcdq,squarefree,scalar_component


def desc(u, na, sh, o):
    E, pp, A, B = geom(u, na, sh, o)
    F, V = constraints(E, pp, A, B)
    Vr = V.real.astype(int)
    assert pp[0][0] == 'sign' and np.all(V.imag == 0)
    S = [j for j in range(5) if E[2][j] != -1]
    J = [j for j in range(5) if j not in S]
    assert len(S) == 2 and len(J) == 3 and all((j in J for j in (*A, *B)))
    T = np.zeros((5, 3), dtype=int)
    d = A[0]
    other = [j for j in J if j != d]
    for k, j in enumerate(other, 1):
        T[j, k] = 1
        T[d, k] = int(j in B) - int(j in A)
    forms = [[(1, 0), (0, 0), (0, 0)]] + [list(map(full.zz, T[j])) for j in J] + [list(map(full.zz, T[list(A)].sum(0)))]
    con = []
    totals = []
    e0 = np.array([1, 0, 0], dtype=int)
    for k in range(2):
        tag, i, k, P, Q, ori, c = pp[k + 1]
        if tag != 'unicolor':
            return
        assert c in (0, 2)
        c = 1 if c == 0 else -1
        Tfull = Vr[k] @ T
        P0 = Vr[k, list(P)] @ T[list(P)]
        R = [j for j in J if j not in (*P, *Q)]
        r = Vr[k, R] @ T[R] if R else np.zeros(3, dtype=int)
        T0 = c * e0 + Tfull
        totals.append(T0)
        q = c * np.outer(T0, P0) + np.outer(e0, Vr[k, list(Q)] @ T[list(Q)]) - np.outer(T0, e0)
        poly = {}
        for a in range(3):
            for b in range(a, 3):
                w = q[a, b] if a == b else q[a, b] + q[b, a]
                if w:
                    poly[tuple((int(i == a) + int(i == b) for i in range(3)))] = w
        con.append(poly)
    forms.extend((list(map(full.zz, r)) for r in [*totals, totals[0] + totals[1], totals[0] - totals[1]]))
    return (V, pp, A, B, S, J, T, con, forms)


def finite2(x):
    V, pp, A, B, S, J, T, con, forms = x
    n = 3
    d = 4
    a, b = raw_mac(3, d, con)
    v = full.lift(a, b, full.EXTENDED)
    if v is None:
        return ('lift', 0)
    K = v[0]
    while K and d >= 2:
        M, _ = full.multiplication(K, n, d)
        if M is not None:
            H = sparse.check_open(M, forms)
            if H is None:
                return ('empty', 0)
            N = full.compressed(M, H)
            size = len(N[0][0])
            I = np.eye(size, dtype=object)
            Z = np.zeros_like(I)
            base = []
            sl = []
            for j in range(5):
                if j in S:
                    c = int(V[2, j].real)
                    base.append(full.scale((c, 0), N[0]))
                    sl.append((c * (1 if j == S[0] else -1) * I, Z))
                else:
                    base.append(full.add_many([full.scale((int(2 * h), 0), v) for h, v in zip(T[j], N)]))
                    sl.append((Z, Z))
            for p in (65521, 1009):

                def G(t):
                    return gram(V, pp, A, B, [full.add_many([v, full.scale((t, 0), g)]) for v, g in zip(base, sl)], p)
                g = G(0)
                z = (G(1) - g) % p
                assert np.array_equal((g + 4 * z) % p, G(2))
                pol = []
                top = False
                for seed in range(18):
                    rr = Random(seed)
                    R = np.array([[rr.randrange(-7, 8) for j in range(9)] for a in range(7)], np.int64)
                    Fg, Fz = [np.einsum('ia,abuv,jb->iujv', R, h, R).reshape(7 * size, 7 * size) % p for h in (g, z)]
                    deg = 2 * size
                    f = full.interpolate([full.determinant((Fg + t * Fz) % p, p) for t in range(deg + 1)], p)
                    top |= len(f) == deg + 1
                    if f:
                        pol = full.poly_gcd(pol, f, p)
                    if top and pol == [1]:
                        return ('pencil', size)
            return ('residual', size)
        K, _ = full.shrink(K, n, d, forms)
        d -= 1
        if K is None:
            return ('shrink', 0)
    return ('empty' if not K else 'curve', len(K))


def fg(V, pp, A, B, W):
    b = len(W[0])
    I = np.eye(b, dtype=object)
    vr = V.real.astype(int)
    v = vr[:, :, None, None] * np.array(W, dtype=object)[None, :, :, :]
    s = v.sum(1)
    F = np.zeros((9, 4, 5, b, b), dtype=object)
    for i in range(3):
        F[i, i] = v[i]
    for j in A:
        F[3, 3, j] = W[j]
    for j in B:
        F[4, 3, j] = W[j]
    for n, (tag, i, k, P, Q, o, c) in enumerate(pp, 5):
        if tag == 'sign':
            for j in range(5):
                F[n, i, j] = -s[k] @ v[k, j]
                F[n, k, j] = s[i] @ v[i, j]
        else:
            v0 = 1 if c == 0 else -1
            for j in P:
                F[n, i, j] = v0 * (s[k] @ v[k, j])
            for j in Q:
                F[n, k, j] = s[i] @ v[k, j]
    F[8] = I
    L = np.stack([F[0] - F[1] + F[2], F[5] - s[0] @ F[1] + s[1] @ F[0], F[3], F[4], F[6], F[7], F[8]])
    K = np.kron(np.kron(3 * np.eye(4, dtype=int) - 1, 4 * np.eye(5, dtype=int) - 1), I)
    a = L.reshape(7, 20, b, b).transpose(0, 2, 1, 3).reshape(7 * b, 20 * b)
    q = F.reshape(9, 20, b, b).transpose(1, 2, 0, 3).reshape(20 * b, 9 * b)
    return a @ K @ q


def exc(data):
    u, na, sh, o = data
    E, pp, A, B = geom(u, na, sh, o)
    _, V = constraints(E, pp, A, B)
    assert E[1] == (0, 0, 0, 2, 2) and E[2] == (-1, -1, -1, 0, 0) and (A == (0,))
    P, Q = pp[1][3:5]
    U, R = pp[2][3:5]
    assert set(P) | set(Q) == set(U) | set(R) == {0, 1, 2}
    if u == 2:
        assert B == (1,) and [int(0 in P) + int(1 in P), int(2 in P)] == [int(0 in U) + int(1 in U), int(2 in U)]
    else:
        assert B == (1, 2) and set(P) in ({0}, {1, 2}) and (set(U) in ({0}, {1, 2}))
    b = 1 if u == 2 else 2
    I = np.eye(b, dtype=object)
    Z = np.zeros((b, b), dtype=object)

    def w(t):
        if u == 2:
            pp0 = 2 * (t * t - 1) if 2 in P else 2
            qq = 2 * t * t - 2 * pp0
            return [pp0 * I, pp0 * I, qq * I, t * I, t * I]
        p = np.array([[0, 1], [2, 0]], dtype=object)
        return [p, t * I, p - t * I, I, I]
    deg = 56 if u == 2 else 28
    mats = [fg(V, pp, A, B, w(t)) for t in range(deg + 1)]
    W = w(2)
    val = fg(V, pp, A, B, [*W[:3], W[3] + I, W[4] - I])
    assert np.array_equal(val, mats[2])
    common = []
    for J in combinations(range(9), 7):
        jj = [j * b + r for j in J for r in range(b)]
        f = inter([idet(a[:, jj].tolist()) for a in mats])
        if f:
            common = gcdq(common, primitive(f))
        if len(common) == 1:
            break
    if u == 2:
        forms = [[0, 1], [1, 1], [-1, 1]]
        if 2 in P:
            forms += [[-1, 0, 1], [2, 0, -1]]
        else:
            forms += [[-2, 0, 1]]
        common = remove(common, forms)
    return common


def spec(u, na, sh, o):
    E, pp, A, B = geom(u, na, sh, o)
    _, V = constraints(E, pp, A, B)
    V = V.real.astype(int)
    S = [j for j in range(5) if V[2, j]]
    J = [j for j in range(5) if j not in S]
    com = next((q for q in pp if q[0] == 'unicolor'))
    sp = next((q for q in pp if q[0] == 'sparse'))
    _, _, k, P, Q, _, ce = com
    c = 1 if ce == 0 else -1
    sig = [int(c * V[k, j]) for j in J]
    h = [(int(j in A) - int(j in B)) * sg for j, sg in zip(J, sig)]
    a, b = next(((a, b) for a in range(3) for b in range(a) if h[a] != h[b]))
    d = 3 - a - b
    v = tower.Rat([0, 1])
    t = tower.Rat([0, 1])

    def row(th, z):
        y = [tower.Rat(0) for j in J]
        y[d] = z
        y[a] = (-h[d] * z - h[b] * (th - z)) / (h[a] - h[b])
        y[b] = th - z - y[a]
        return y
    cc = row(t, tower.Rat(0))
    ll = [b - a for a, b in zip(cc, row(t, tower.Rat(1)))]

    def con(ys):
        return sum((t * y if j in P else -y if j not in Q else tower.Rat(0) for j, y in zip(J, ys)), tower.Rat(0))
    alpha = con(ll)
    beta = 1 - con(cc)
    return (E, pp, A, B, V, S, J, sig, sp, cc, ll, alpha, beta)


def polynomial_chart(w, V, sp, S, J):
    _, _, k, P, Q, _, _ = sp
    assert len(P) == len(Q) == 1
    h = int(V[2, P[0]] * V[k, P[0]])
    den, nn = tower.common_den(w)
    wt = [None] * 5
    for j, n in zip(J, nn):
        wt[j] = (tower.mulint(n, 2), [], [], [])
    sig = lambda j: int(V[2, j])
    wt[P[0]] = (tower.mulint(den, 2 * sig(P[0])), [sig(P[0])], [], [])
    wt[Q[0]] = ([], [-sig(Q[0])], [], [])
    T = reduce(tower.plus, (tower.mulint(n, int(h * V[k, j])) for j, n in zip(J, nn)), [])
    return ((T, tower.mulint(tower.times(den, den), -2)), None, wt)


def norm_projected(chart, V, pp, P, t):
    first, second, weights = chart
    add, sc, mul, norm, one, zero = tower.ring(first, second, t)
    ws = [tower.ring_weight(w, first, second, t) for w in weights]
    v = [[sc(x, int(c)) for x, c in zip(ws, row)] for row in V]

    def sm(z):
        return reduce(add, z, zero)
    sums = list(map(sm, v))
    F = [[zero] * 20 for _ in range(9)]
    for i in range(3):
        for j in range(5):
            F[i][5 * i + j] = v[i][j]
    for j in ACTIVE_A:
        F[3][15 + j] = ws[j]
    for j in ACTIVE_B:
        F[4][15 + j] = ws[j]
    for q, (tag, i, k, B, C, ori, ce) in enumerate(pp, 5):
        if tag == 'sign':
            for j in range(5):
                F[q][5 * i + j] = sc(mul(sums[k], v[k][j]), -1)
                F[q][5 * k + j] = mul(sums[i], v[i][j])
        elif tag == 'sparse':
            for j in C:
                F[q][5 * i + j] = mul(sums[k], v[i][j])
            for j in B:
                F[q][5 * k + j] = mul(sums[i], v[k][j])
        else:
            for j in B:
                F[q][5 * i + j] = sc(mul(sums[k], v[k][j]), 1 if ce == 0 else -1)
            for j in C:
                F[q][5 * k + j] = mul(sums[i], v[k][j])
    F[8] = [one] * 20
    Z = [[sm((sc(row[j], v) for v, row in zip(proj, F) if v)) for j in range(20)] for proj in P]
    U = []
    for rr in Z:
        rs = [sm(rr[5 * i:5 * i + 5]) for i in range(4)]
        cs = [sm(rr[j::5]) for j in range(5)]
        s = sm(rs)
        U.append([sm((sc(x, 12), sc(rs[j // 5], -3), sc(cs[j % 5], -4), s)) for j, x in enumerate(rr)])
    GG = [[zero] * 7 for i in range(7)]
    for i in range(7):
        for j in range(i + 1):
            GG[i][j] = GG[j][i] = sm((mul(a, b) for a, b in zip(Z[i], U[j]) if a != zero and b != zero))
    layer = {0: one}
    for i in range(7):
        nxt = {}
        for mask, h in layer.items():
            for j, entry in enumerate(GG[i]):
                if mask >> j & 1 or entry == zero:
                    continue
                q = mask | 1 << j
                term = mul(h, entry)
                if (mask >> j + 1).bit_count() % 2:
                    term = sc(term, -1)
                nxt[q] = add(nxt.get(q, zero), term)
        layer = nxt
    return norm(layer.get(127, zero))


def norm_poly(ch, V, pp, seed):
    P, b, c = projection(seed)
    W = tower.bound_chart(ch)
    sheets = 2 ** sum((x is not None for x in ch[:2]))
    bound = (factorial(7) * (20 ** 2 * 6 * 77 ** 2) ** 7 * 5 ** (2 * c) * W ** (2 * (b + 2 * c))) ** sheets
    bits = bound.bit_length() + 2
    value = norm_projected(ch, V.real.astype(int).tolist(), pp, P, 1 << bits)
    coeff = []
    base = 1 << bits
    half = base // 2
    while value:
        q, r = divmod(value + half, base)
        r -= half
        assert abs(r) <= bound
        coeff.append(r)
        value = q
    return primitive(coeff)


def normset(ch, V, pp):
    weights = ch[2]
    vr = V.real.astype(int)

    def row(vals):
        return [reduce(plus, (tower.mulint(w[j], int(a)) for a, w in zip(vals, weights)), []) for j in range(4)]
    forms = [*weights, *[row(v) for v in vr], row(vr[0] + vr[1]), row(vr[0] - vr[1])]
    if any((not any(e) for e in forms)):
        return [1]
    common = []
    for j in range(10):
        h = norm_poly(ch, V, pp, j)
        if h:
            old = common
            common = gcdq(common, squarefree(h))
            if len(common) == 1 or common == old or j >= 2:
                break
    return common


projection=mx.projection


def checkm(V, pp, A, B, W):
    M = tower.rational_mats(W)

    def z(r):
        return [(int(x), 0) for x in r]
    forms = [z(r) for r in np.eye(5, dtype=int)] + [z(r) for r in V] + [z(V[0] - V[1]), z(V[0] + V[1]), z([int(j in A) for j in range(5)])]
    H = sparse.check_open(M, forms)
    if H is None:
        return 'empty'
    N = full.compressed(M, H)
    d = len(N[0][0])
    for p in (65521, 1009):
        G = gram(V, pp, A, B, N, p)
        for seed in range(8):
            rr = Random(seed)
            R = np.array([[rr.randrange(-7, 8) for j in range(9)] for a in range(7)], np.int64)
            F = np.einsum('ia,abuv,jb->iujv', R, G, R).reshape(7 * d, 7 * d) % p
            if full.full_rank(F, p):
                return 'gram'
    return 'unresolved'


def wf(V, pp, A, B, S, J, sp, w, t):
    _, _, k, P, Q, _, _ = sp
    h = int(V[2, P[0]] * V[k, P[0]])
    I = np.eye(len(t), dtype=object)
    ww = [None] * 5
    T = sum((int(V[k, j]) * a for j, a in zip(J, w)), np.zeros_like(I))
    z = tower.quad(h * T, -2 * I)
    I = tower.duplicate(I)
    for j, a in zip(J, w):
        ww[j] = tower.duplicate(a)
    ww[P[0]] = int(V[2, P[0]]) * (2 * I + z) * Fraction(1, 2)
    ww[Q[0]] = -int(V[2, Q[0]]) * z * Fraction(1, 2)
    return checkm(V, pp, A, B, ww)


def quadratic_vertical(V, pp, A, B, S, J, sp, sig, cc, ll, g):
    assert g == [-2, 0, 1]
    _, _, k, P, Q, _, _ = sp
    h = int(V[2, P[0]] * V[k, P[0]])
    cs = [tower.scalar_component(z, g) for z in cc]
    ls = [tower.scalar_component(z, g) for z in ll]
    assert all((not a[0] and (not b[1]) for a, b in zip(cs, ls)))
    den = lcm(*(v.denominator for m in [*cs, *ls] for v in m))
    w = [None] * 5
    four = []
    for j, sg, a, b in zip(J, sig, cs, ls):
        c = sg * int(den * a[1])
        l = sg * int(den * b[0])
        four.append((c, l))
        w[j] = ([0, 2 * l], [2 * c], [], [])
    n0 = sum((int(V[k, j]) * b for j, (a, b) in zip(J, four)))
    n1 = sum((int(V[k, j]) * a for j, (a, b) in zip(J, four)))
    first = ([0], [-2])
    second = ([0, h * n0], [h * n1], [-2 * den * den])
    w[P[0]] = ([2 * den * int(V[2, P[0]])], [], [int(V[2, P[0]])], [])
    w[Q[0]] = ([], [], [-int(V[2, Q[0]])], [])
    q = normset((first, second, w), V, pp)
    if not q:
        return 'vertical-zero-norm'
    if len(q) == 1:
        return 'vertical-curve-empty'
    T = tower.comp(g)
    U = tower.comp(q)
    t = np.kron(T, np.eye(len(U), dtype=object))
    u = np.kron(np.eye(len(T), dtype=object), U)
    miss = [(a * t + b * u) * Fraction(1, den) for a, b in four]
    return 'vertical-' + wf(V, pp, A, B, S, J, sp, miss, t)


def proceed(dat):
    global ACTIVE_A, ACTIVE_B
    E, pp, A, B, V, S, J, sig, sp, cc, ll, alpha, beta = spec(*dat)
    ACTIVE_A = A
    ACTIVE_B = B

    def oncurve(w):
        ch = polynomial_chart(w, V, sp, S, J)
        q = normset(ch, V, pp)
        if not q:
            return 'zero-norm'
        den, _ = tower.common_den(w)
        q = tower.remove(q, [den])
        if len(q) <= 1:
            return 'curve-empty'
        t = tower.comp(q)
        return wf(V, pp, A, B, S, J, sp, [tower.rmat(y, t, q) for y in w], t)
    out = []
    if alpha.n:
        v = beta / alpha
        w = [e * (a + b * v) for e, a, b in zip(sig, cc, ll)]
        out.append(oncurve(w))
        vert = gcdq(alpha.n, beta.n)
    else:
        vert = squarefree(beta.n)
    if len(vert) > 1:
        if len(vert) > 2:
            out.append(quadratic_vertical(V, pp, A, B, S, J, sp, sig, cc, ll, vert))
            return out
        t = Fraction(-vert[0], vert[1])
        v = tower.Rat([0, 1])

        def at(y):
            return sum((a * t ** j for j, a in enumerate(y.n))) / sum((a * t ** j for j, a in enumerate(y.d)))
        w = [e * (tower.Rat(at(a)) + tower.Rat(at(b)) * v) for e, a, b in zip(sig, cc, ll)]
        out.append('vertical-' + oncurve(w))
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=('all','finite','curves'),default='all')
    parser.add_argument('--shard',nargs=2,type=int,default=[0,1])
    args=parser.parse_args();idx,tot=args.shard
    assert 0<=idx<tot
    counts=Counter();detail=Counter();ret=0
    for u,na,sh,o,E,pp,A,B in mixed.iter_all(False):
        if sum(s!=-1 for h,s in sh)!=2:continue
        F,V=constraints(E,pp,A,B)
        if not sparse.passes(F):continue
        hit=ret%tot==idx;ret+=1
        if not hit:continue
        dat=(u,na,sh,o)
        if pp[0][0]=='three':
            if args.part=='curves':continue
            tag,n=mixed.finite(*dat,False);assert tag in ('gram','excluded');counts['finite '+tag]+=1
        else:
            if args.part=='finite':continue
            n=sum(q[0]=='unicolor'for q in pp)
            if n==2:
                tag,b=finite2(desc(*dat))
                if tag=='curve':
                    assert exc(dat)==[1];tag='split-independent'
                assert tag in ('empty','pencil','split-independent'),(dat,tag)
                counts['common '+tag]+=1
            else:
                assert n==1
                rr=proceed(dat);assert rr and all(y in ('empty','gram','curve-empty','vertical-curve-empty','vertical-empty','vertical-gram')for y in rr),(dat,rr)
                detail.update(rr);counts['one common']+=1
    assert ret==1974
    if tot==1 and args.part!='finite':assert counts['one common']==96 and counts['common empty']==126 and counts['common pencil']==262 and counts['common split-independent']==6
    if tot==1 and args.part!='curves':assert counts['finite gram']==376 and counts['finite excluded']==1108
    print('Retained',ret,'verified',dict(counts),'one-common branches',dict(detail),flush=True)

if __name__=='__main__':
    main()
