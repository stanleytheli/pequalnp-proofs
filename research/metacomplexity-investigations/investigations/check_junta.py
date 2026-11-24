"""Check the scope-gluing lemma, width certificates and the zero-gate realization."""
from itertools import combinations, product
from random import Random


def represented(n, scope):
    masks = [sum(((x >> i)&1) << j for j,i in enumerate(scope)) for x in range(1 << n)]
    for rule in range(1 << (1 << len(scope))):
        yield tuple((rule >> m)&1 for m in masks)


def rows():
    n,q = 4,2
    scopes = list(combinations(range(n),q))
    by_scope = {a:list(represented(n,a)) for a in scopes}
    total = 0
    defined = 0
    for a,b in product(scopes,repeat=2):
        ma = sum(1 << i for i in a)
        mb = sum(1 << i for i in b)
        for p,v in product(by_scope[a],by_scope[b]):
            if any(j>i for i,j in zip(p,v)):
                continue
            total += 1
            table = tuple(x+y for x,y in zip(p,v))   # 0 absent, 1 zero, 2 one
            for x,val in enumerate(table):
                if val:
                    assert any(all(table[y]==val for y in range(1<<n) if not ((x^y)&scope))
                               for scope in (ma,mb))
                    defined += 1
    return total,defined


def clause_ok(clause, x):
    return any((bool(x & (1 << (abs(lit)-1))) == (lit>0)) for lit in clause)


def union_controls():
    rng = Random(7153)
    tests = 0
    for n in range(1,6):
        for d in range(1,6):
            for _ in range(14):
                cnfs = [[[rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randint(0,2))]
                         for _ in range(rng.randrange(0,6))] for _ in range(d)]
                width = max(map(len,cnfs)).bit_length()
                mask = (1 << d)-1
                for x in range(1 << n):
                    prescribed = {0:0,mask:1}
                    for j,clauses in enumerate(cnfs):
                        for t,clause in enumerate(clauses,1):
                            row = (mask ^ (1 << j)) | (t << d)
                            assert row and row != mask
                            if not clause_ok(clause,x):
                                prescribed[row] = 1
                    survivors = {j for j in range(d+width)
                                 if all(((row >> j)&1)==v for row,v in prescribed.items())}
                    expected = {j for j,clauses in enumerate(cnfs)
                                if all(clause_ok(c,x) for c in clauses)}
                    assert survivors == expected
                    tests += 1
    return tests


def parity_cells():
    tests = 0
    for q,m in [(1,4),(2,3),(3,3),(4,2)]:
        n = q*m
        counts = {}
        for x in range(1 << n):
            key = tuple(bin((x >> (i*q)) & ((1<<q)-1)).count("1")%2 for i in range(m))
            if sum(key)%2:
                counts[key] = counts.get(key,0)+1
        assert len(counts)==1 << (m-1) and set(counts.values())=={1 << (n-m)}
        tests += sum(counts.values())
    return tests


def zero_size_optimum():
    cases = 0
    for m,q in [(3,1),(3,2),(3,3),(4,1),(4,2),(5,1),(5,2)]:
        even = [y for y in range(1,1<<m) if bin(y).count("1")%2==0]
        arity = len(even)
        assert arity == (1 << (m-1))-1
        rows = [sum(((y >> i)&1) << j for j,y in enumerate(even)) for i in range(m)]
        assert len(set(rows)) == m
        patterns = {0}
        for j in range(arity):
            patterns.add(sum(((row >> j)&1) << i for i,row in enumerate(rows)))
        assert patterns == {0,*even}
        # Exercise all source assignments and every candidate on the actual rows.
        for x in range(1 << (m*q)):
            target = 1
            for i in range(m):
                target ^= (bin((x >> (i*q)) & ((1 << q)-1)).count("1")%2) << i
            assert (target in patterns) == bool(bin(x).count("1")%2)
            cases += 1
        if m <= 4:
            codes = [(0,0)]*(1 << arity)
            for i,row in enumerate(rows):
                codes[row] = (1,(5 >> i)&1)
            encoded = [0]+[c for row in codes for c in row]
            assert len(encoded)==1+(1 << (1 << (m-1)))
    return cases


if __name__ == '__main__':
    legal,certs = rows()
    print(f'{legal} legal pairs of two-juntas on four bits, {certs} defined-row certificates checked')
    print(f'{union_controls()} CNF-union inputs: all surviving zero-gate projections match exactly')
    print(f'{parity_cells()} odd inputs checked for sharp block-parity witness multiplicities')
    print(f'{zero_size_optimum()} source inputs checked on the exact minimum-arity zero-gate construction')
