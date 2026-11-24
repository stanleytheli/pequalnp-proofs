"""Independent finite controls for one-hot support, signed gaps and border faces."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import prod


def circuits():
    nodes = []
    def node(kind, *args):
        nodes.append((kind, args))
        return len(nodes)-1
    x = [[node("bit", i, b) for b in range(2)] for i in range(3)]
    zero, one = node("zero"), node("parameter", 0)
    small, large = node("parameter", 1), node("parameter", 2)
    # The first summand tends to infinity as a polynomial and vanishes on all one-hot masks.
    inconsistent = node("times", x[0][0], x[0][1], large)
    # The shared subcircuit may diverge on every input. Normalization occurs several levels later.
    huge = node("times", large, large)
    tiny = node("times", small, small)
    kept = node("times", x[0][0], x[1][0], huge, tiny)
    rare = node("times", x[0][1], x[1][0], small)
    sumgate = node("plus", kept, rare)
    shared = node("times", sumgate, sumgate)
    # In a complete loop-free triangle there are precisely two directed 3-cycles.
    hamilton = node("hc", (zero, shared, x[0][1]), (x[1][1], zero, one), (one, x[2][1], zero))
    root = node("plus", inconsistent, hamilton)
    return nodes, root


def alternatives(row):
    kind, data = row
    if kind == "plus":
        return [(child,) for child in data]
    if kind == "times":
        return [data]
    tails = len(data)
    result = []
    # Explicitly enumerate cyclic orders, independently of any permutation DP.
    for order in permutations(range(1, tails)):
        cycle = (0,)+order
        result.append(tuple(data[cycle[j]][cycle[(j+1)%tails]] for j in range(tails)))
    return result


def expand(nodes, root, mask):
    poly = []
    for kind, data in nodes[:root+1]:
        if kind == "bit":
            terms = Counter({(0,0,0):1}) if mask[data[0]]==data[1] else Counter()
        elif kind == "parameter":
            terms = Counter({tuple(int(i==data[0]) for i in range(3)):1})
        elif kind == "zero":
            terms = Counter()
        else:
            terms = Counter()
            for option in alternatives((kind,data)):
                part = Counter({(0,0,0):1})
                for child in option:
                    nxt = Counter()
                    for a,p in part.items():
                        for b,q in poly[child].items():
                            nxt[tuple(x+y for x,y in zip(a,b))] += p*q
                    part = nxt
                terms.update(part)
        poly.append(terms)
    return poly[root]


def policy_max(nodes, root, mask, objective):
    values = []
    for kind,data in nodes[:root+1]:
        if kind=="bit":
            best=0 if mask[data[0]]==data[1] else None
        elif kind=="parameter":
            best=objective[data[0]]
        elif kind=="zero":
            best=None
        else:
            feasible=[sum(values[v] for v in option) for option in alternatives((kind,data))
                      if all(values[v] is not None for v in option)]
            best=max(feasible,default=None)
        values.append(best)
    return values[root]


def border_check():
    nodes, root = circuits()
    masks = tuple(product(range(2), repeat=3))
    rows = {b:expand(nodes,root,b) for b in masks}
    allterms = {a for row in rows.values() for a in row}
    surviving = {a for a in allterms if a[1]==a[2]}
    assert surviving and allterms-surviving and all(a[1]>=a[2] for a in allterms)
    def score(w,a):
        return sum(x*y for x,y in zip(w,a))
    for w in product(range(-3,4),repeat=3):
        top=max(score(w,a) for a in allterms)
        if {a for a in allterms if score(w,a)==top}==surviving:
            break
    else:
        raise AssertionError("no exposing integral objective")
    for b,row in rows.items():
        weight=sum(v for a,v in row.items() if a in surviving)
        assert (weight>0)==((b[0],b[1])==(0,0) or b==(1,1,1))
        assert (policy_max(nodes,root,b,w)==top)==(weight>0)
        for t in (Fraction(1,2),Fraction(1,17),Fraction(1,101)):
            concrete=sum(v*t**(a[1]-a[2]) for a,v in row.items())
            assert concrete>=weight
            assert concrete-weight <= t*sum(row.values())
    return len(masks),len(allterms),len(surviving)


def gap_check():
    inputs=list(product(range(2),repeat=4))
    witnesses=list(product(range(2),repeat=3))
    def sign(b,z):
        a=sum(x*y for x,y in zip(b,z))%2
        c=((sum(z)+b[-1])%3==0) if b[0] else bool(a)
        return int(a)-int(c)
    coefficients={b:sum(sign(b,u)*sign(b,v) for u in witnesses for v in witnesses) for b in inputs}
    for b in inputs:
        gap=sum(sign(b,z) for z in witnesses)
        assert coefficients[b]==gap*gap
        value=sum(c*prod(int(x==y) for x,y in zip(b,d)) for d,c in coefficients.items())
        assert (value>0)==(gap!=0)
    assert any(c==0 for c in coefficients.values())
    return len(inputs),sum(c>0 for c in coefficients.values())


if __name__=="__main__":
    print("border masks, consistent exponent vectors, surviving vectors:",*border_check())
    print("gap masks, nonzero coefficients:",*gap_check())
