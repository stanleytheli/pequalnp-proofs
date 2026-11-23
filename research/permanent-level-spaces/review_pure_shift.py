"""Independent determinant and restricted-rank check for the pure shift review.

The existing certificate supplies the enumerated roots.  The second-order form is
written directly in a coordinate-difference basis.  The linear constraints are
coefficients of derivatives of the original injective permanent, calculated from
its 120 summands.  This check does not use the certificate's polarization,
Fourier tangent basis, or bordered matrix.
"""
from collections import Counter
from itertools import permutations, combinations
import pure_column_shift_certificate as cert


def exact_discriminant():
    """After cancellation of 5^5 the Fourier Gram determinant is integral."""
    terms = Counter()
    for sigma in permutations(range(5)):
        sign = (-1) ** sum(x > y for x, y in combinations(sigma, 2))
        counts = [0, 0, 0]
        val = sign
        for i, j in enumerate(sigma):
            m = (-i-j) % 5
            if m > 2:
                break
            counts[m] += 1
            val *= 4-m if (-i) % 5 <= m else -(m+1)
        else:
            terms[tuple(counts)] += val
    return {k: v for k, v in terms.items() if v}


def pivot_reduce(rows):
    a = [r[:] for r in rows]
    piv = []
    for col in range(len(rows[0])):
        unused = next((r for r in range(len(piv), len(a)) if a[r][col]), None)
        if unused is None:
            continue
        p = len(piv)
        a[p], a[unused] = a[unused], a[p]
        a[p] = [x / a[p][col] for x in a[p]]
        for r in range(len(a)):
            if r != p and a[r][col]:
                fac = a[r][col]
                a[r] = [x-fac*y for x, y in zip(a[r], a[p])]
        piv.append(col)
        if len(piv) == len(a):
            break
    return a, piv


def rank_with_derivatives(c):
    F = c[0].F
    zero, unit = F.val(0), F.val(1)
    rho = [pow(cert.fourth, r, cert.P) for r in range(4)]
    pairs = [(a, b) for a in range(1, 4) for b in range(4-a)]
    d = {power: [zero]*15 for power in pairs}
    for colmap in permutations(range(5), 4):
        for special, j in enumerate(colmap):
            poly = {(0,0): unit}
            for row, col in enumerate(colmap):
                if row == special:
                    continue
                out = poly.copy()
                for (a, b), coeff in poly.items():
                    for increment, term in [((1,0), rho[row]*c[col]), ((0,1), cert.roots[col])]:
                        key = (a+increment[0], b+increment[1])
                        out[key] = out.get(key, zero) + term*coeff
                poly = out
            for p in pairs:
                for i in range(3):
                    sign = int(special == i) - int(special == 3)
                    if sign:
                        d[p][5*i + j] += sign*poly[p]
    red, piv = pivot_reduce(list(d.values()))
    free = sorted(set(range(15)) - set(piv))
    ker = []
    for j in free:
        v = [zero]*15
        v[j] = unit
        for i, k in enumerate(piv):
            v[k] = -red[i][j]
        ker.append(v)
    # T3(Y,Z,B) in centered row differences e_i-e_3, times an irrelevant scalar.
    q = [[0 if i%5 == j%5 else (1+int(i//5 == j//5))*(cert.roots[i%5] + cert.roots[j%5])
          for j in range(15)] for i in range(15)]
    qker = [[sum((a*qij for a, qij in zip(v, row)), zero) for row in q] for v in ker]
    r = [[sum((a*b for a, b in zip(v, w)), zero) for w in qker] for v in ker]
    _, rpiv = pivot_reduce(r)
    assert len(rpiv) > 2*(len(free)-6)
    return len(piv), len(rpiv), 2*len(piv)+len(rpiv)


def main():
    det = exact_discriminant()
    assert det == {(5,0,0):4, (0,5,0):-72, (0,0,5):72, (1,3,1):220, (2,1,2):-140}
    print("Integer determinant", sorted(det.items()), flush=True)
    ranks = Counter()
    for f in cert.factor(cert.primary("quartic")):
        F = cert.Field(f)
        for _, _, c in cert.genuine_points(F.val([0,1]), "quartic"):
            ranks[rank_with_derivatives(c)] += F.n
    for _, c in cert.check_infinity("quartic"):
        ranks[rank_with_derivatives(c)] += 1
    print("Ranks (D, Q on ker D, bordered) by point count", ranks, flush=True)
    assert sum(ranks.values()) == 40


if __name__ == "__main__":
    main()
