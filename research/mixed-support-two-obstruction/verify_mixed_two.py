"""Verify the support-two obstruction when both low active coordinates are supported."""
import argparse
from collections import Counter
from functools import reduce
from itertools import product
from math import factorial,lcm
from fractions import Fraction
from random import Random
import numpy as np
import verify_full_rows as full
import verify_sparse_rows as sparse
import verify_mixed_rows as mixed
import verify_support_two as tower
from verify_support_two import gcdq,lcmq,squarefree,primitive,plus,multiply,remove,scalar_component


def charts(V, pp):
    (deg, ns, rep, eq, A, B) = tower.equation(V, pp)
    assert deg >= 0
    (D, rs) = tower.common_den(eq)
    (rs, co) = tower.primitive_common(rs)
    while rs and (not rs[-1]):
        rs.pop()
    if len(rs) <= 1:
        return ([], co, rs[0] if rs else [])
    ld = rs[-1]
    pr = []
    if len(rs) == 2:
        pr = [(tower.Rat(tower.mulint(rs[0], -1), ld), tower.Rat(0), None)]
    else:
        (g0, g1, g2) = rs
        ds = plus(tower.times(g1, g1), tower.mulint(tower.times(g0, g2), -4))
        rt = tower.polysquare(ds)
        if rt is None:
            pr = [(tower.Rat(0), tower.Rat(1, g2), (g1, tower.times(g2, g0)))]
        else:
            for sg in (1, -1) if rt else (1,):
                pr.append((tower.Rat(plus(tower.mulint(g1, -1), tower.mulint(rt, sg)), tower.mulint(g2, 2)), tower.Rat(0), None))
    (c, l, _) = rep
    chs = []
    for (a, b, f) in pr:
        coords = [h for j in (2, 3, 4) for h in (c[j] + l[j] * a, l[j] * b)]
        (den, z) = tower.common_den(coords)
        W = [(den, [], [], []), (den, [], [], [])] + [(tower.mulint(z[2 * k], 2), tower.mulint(z[2 * k + 1], 2), [], []) for k in range(3)]
        chs.append((f, None, W))
    return (chs, co, ld)


def projection(seed):
    rules = ((1, 5, 1), (1, 4, 2), (1, 3, 3), (0, 5, 2), (0, 4, 3))
    (a, b, c) = rules[seed % 5]
    rg = Random(seed + 103)
    P = [[0] * 9 for _ in range(7)]
    if a:
        P[0][8] = 1
    for row in P[a:a + b]:
        row[:5] = [rg.randrange(-7, 8) for j in range(5)]
    for row in P[a + b:]:
        row[5:8] = [rg.randrange(-7, 8) for j in range(3)]
    return (P, b, c)


def norm_projected(chart, V, pp, P, t):
    (first, second, weights) = chart
    (add, sc, mul, norm, one, zero) = tower.ring(first, second, t)
    ws = [tower.ring_weight(w, first, second, t) for w in weights]
    v = [[sc(x, int(c)) for (x, c) in zip(ws, row)] for row in V]

    def sm(z):
        return reduce(add, z, zero)
    sums = list(map(sm, v))
    F = [[zero] * 20 for _ in range(9)]
    for i in range(3):
        for j in range(5):
            F[i][5 * i + j] = v[i][j]
    F[3][15] = ws[0]
    F[4][16] = ws[1]
    for (q, (tag, i, k, B, C, ori)) in enumerate(pp, 5):
        if tag == 'sign':
            for j in range(5):
                F[q][5 * i + j] = sc(mul(sums[k], v[k][j]), -1)
                F[q][5 * k + j] = mul(sums[i], v[i][j])
        else:
            for j in B:
                F[q][5 * i + j] = mul(sums[k], v[k][j])
            for j in C:
                F[q][5 * k + j] = mul(sums[i], v[k][j])
    F[8] = [one] * 20
    Z = [[sm((sc(row[j], v) for (v, row) in zip(proj, F) if v)) for j in range(20)] for proj in P]
    U = []
    for rr in Z:
        rs = [sm(rr[5 * i:5 * i + 5]) for i in range(4)]
        cs = [sm(rr[j::5]) for j in range(5)]
        s = sm(rs)
        U.append([sm((sc(x, 12), sc(rs[j // 5], -3), sc(cs[j % 5], -4), s)) for (j, x) in enumerate(rr)])
    GG = [[zero] * 7 for i in range(7)]
    for i in range(7):
        for j in range(i + 1):
            GG[i][j] = GG[j][i] = sm((mul(a, b) for (a, b) in zip(Z[i], U[j]) if a != zero and b != zero))
    layer = {0: one}
    for i in range(7):
        nxt = {}
        for (mask, h) in layer.items():
            for (j, entry) in enumerate(GG[i]):
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
    (P, b, c) = projection(seed)
    W = tower.bound_chart(ch)
    sheets = 2 ** sum((x is not None for x in ch[:2]))
    bound = (factorial(7) * (20 ** 2 * 6 * 77 ** 2) ** 7 * 5 ** (2 * c) * W ** (2 * (b + 2 * c))) ** sheets
    bits = bound.bit_length() + 2
    value = norm_projected(ch, V.real.astype(int).tolist(), pp, P, 1 << bits)
    coeff = []
    base = 1 << bits
    half = base // 2
    while value:
        (q, r) = divmod(value + half, base)
        r -= half
        assert abs(r) <= bound
        coeff.append(r)
        value = q
    return primitive(coeff)


def normset(ch, V, pp):
    weights = ch[2]
    vr = V.real.astype(int)

    def row(vals):
        return [reduce(plus, (tower.mulint(w[j], int(a)) for (a, w) in zip(vals, weights)), []) for j in range(4)]
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


def checkm(V, pp, W):
    M = tower.rational_mats(W)
    vr = V.real.astype(int)

    def cc(v):
        return [(int(x), 0) for x in v]
    forms = [cc(r) for r in np.eye(5, dtype=int)] + [cc(r) for r in vr] + [cc(vr[0] + vr[1]), cc(vr[0] - vr[1])]
    H = sparse.check_open(M, forms)
    if H is None:
        return 'empty'
    N = full.compressed(M, H)
    if not N:
        return 'compression'
    n = len(N[0][0])
    pp7 = [(*r, 0) for r in pp]
    for p in (65521, 1009):
        G = mixed.gram(V, pp7, (0,), (1,), N, p)
        for seed in range(8):
            rg = Random(seed)
            R = np.array([[rg.randrange(-7, 8) for j in range(9)] for k in range(7)], np.int64)
            U = np.einsum('ia,abuv,jb->iujv', R, G, R).reshape(7 * n, 7 * n) % p
            if full.full_rank(U, p):
                return 'gram'
    return 'unresolved'


def vertical(V, pp, g, rep):
    deg = len(g) - 1
    if deg > 2 or g[-1] != 1:
        return 'vertical-high'
    (C, L, _) = rep
    coeff = [(scalar_component(C[j], g), scalar_component(L[j], g)) for j in (2, 3, 4)]
    den = lcm(*(x.denominator for (a, b) in coeff for r in (a, b) for x in r))
    al = [[tower.trim([int(a[k] * den), int(b[k] * den)]) for k in range(2)] for (a, b) in coeff]
    f = ([g[1]], [g[0]]) if deg == 2 else None
    w = [([den], [], [], []), ([den], [], [], [])] + [(tower.mulint(a, 2), tower.mulint(b, 2), [], []) for (a, b) in al]
    q = normset((f, None, w), V, pp)
    if not q:
        return 'vertical-zero-norm'
    if len(q) == 1:
        return 'vertical-empty'
    T = tower.comp(g)
    P = tower.comp(q)
    m = len(T)
    n = len(P)
    I = np.eye(m * n, dtype=object)
    param = np.kron(np.eye(m, dtype=object), P)
    ww = [np.kron(tower.rmat(C[j], T, g), np.eye(n, dtype=object)) + np.kron(tower.rmat(L[j], T, g), np.eye(n, dtype=object)) @ param for j in (2, 3, 4)]
    return 'vertical-' + checkm(V, pp, [I * tower.Fraction(1, 2), I * tower.Fraction(1, 2), *ww])


def run(j, V, pp):
    (chs, co, ld) = charts(V, pp)
    ans = lcmq([0, 1], squarefree(co) or [1])
    ans = lcmq(ans, squarefree(ld) or [1])
    for ch in chs:
        z = normset(ch, V, pp)
        if not z:
            return ['zero-norm']
        ans = lcmq(ans, z)
    (deg, _, rep, eq, A, B) = tower.equation(V, pp)
    (C, L, _) = rep
    R = [k for k in (2, 3, 4) if k not in (*A[3], *A[4])]
    ans = remove(ans, [[1, 1]] + ([[0, 1]] if not R else []))
    if len(ans) <= 1:
        return ['no-fibre']
    (den, rs) = tower.common_den(eq)
    assert len(gcdq(den, ans)) == 1
    cond = ans
    out = []
    for de in (2, 1, 0):
        (z, nz) = tower.refine(cond, rs[de])
        cond = z
        if len(nz) <= 1:
            continue
        if not de:
            out.append('inconsistent')
            continue
        T = tower.comp(nz)
        I = np.eye(len(T), dtype=object)
        c = [tower.rmat(h, T, nz) for h in C]
        l = [tower.rmat(h, T, nz) for h in L]
        inv = tower.invmod(rs[de], nz)
        if de == 1:
            v = tower.polmat(tower.polydiv(multiply([-x for x in rs[0]], inv), nz)[1], T)
        else:
            v = tower.quad(tower.polmat(tower.polydiv(multiply(rs[1], inv), nz)[1], T), tower.polmat(tower.polydiv(multiply(rs[0], inv), nz)[1], T))
            c = tower.duplicate(c)
            l = tower.duplicate(l)
        missing = [a + b @ v for (a, b) in zip(c[2:], l[2:])]
        I = np.eye(len(v), dtype=object) * tower.Fraction(1, 2)
        out.append(checkm(V, pp, [I, I, *missing]))
    if len(cond) > 1:
        out.append(vertical(V, pp, cond, rep))
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=('all','finite','curves'),default='all')
    parser.add_argument('--shard',nargs=2,type=int,default=[0,1],metavar=('INDEX','COUNT'))
    args=parser.parse_args();idx,tot=args.shard
    assert tot>0 and 0<=idx<tot
    retained=0;counts=Counter();details=Counter()
    for u,na,shape,ori,E,pp,A,B in mixed.iter_all(True):
        if sum(s!=-1 for e,s in shape)!=2:continue
        assert u==2 and na==1 and tuple(A)==(0,) and tuple(B)==(1,)
        F,V=mixed.constraints(E,pp,A,B)
        if not sparse.passes(F):continue
        use=retained%tot==idx;retained+=1
        if not use:continue
        if pp[0][0]=='three':
            if args.part in ('finite','all'):
                tag,n=mixed.finite(u,na,shape,ori,True)
                assert tag in ('gram','excluded'),(shape,ori,tag)
                counts[tag]+=1
        else:
            assert pp[0][0]=='sign' and all(q[0]=='unicolor' and q[-1]==0 for q in pp[1:])
            if args.part in ('curves','all'):
                result=run(0,V,[q[:6]for q in pp])
                assert all(t in ('gram','empty','inconsistent','no-fibre','vertical-gram','vertical-empty') for t in result),(shape,ori,result)
                details.update(result);counts['curve']+=1
    assert retained==1834
    if tot==1 and args.part in ('finite','all'):assert counts['gram']==1538 and counts['excluded']==16
    if tot==1 and args.part in ('curves','all'):assert counts['curve']==280
    print('Retained',retained,'verified',dict(counts),'curve fibre cases',dict(details),flush=True)

if __name__=='__main__':
    main()
