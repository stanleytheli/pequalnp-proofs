"""Verify the two-baseline compiler and the arithmetic read-once obstruction."""
from collections import Counter
from itertools import combinations, product
from functools import lru_cache

from layered import paired_layers, dualized_gates
from check_layered import shape, extend_unique
from check_gap import all_bits, sat, tours
from succinct_gap import planted


def check_dual(formula, count, order):
    net, _, rails, edges, out = planted(formula,count,order)
    conditions, phase = dualized_gates(net,out)
    encoded = paired_layers(conditions,phase)
    shape(encoded)
    projected = {a: Counter() for a in all_bits(count) if sat(formula,a)}
    supports = set()
    for primary in all_bits(net.primary_count):
        logical = net.evaluate(primary)
        for r in (False, True):
            absolute = [False,*[bool(v)^r for v in logical[1:]],r]
            accepted = bool(logical[out] and (not r or logical[1]))
            assert all(any(absolute[abs(l)] == (l>0) for l in clause) for clause in conditions) == accepted
            # Construct once for every accepted model and separately enumerate
            # the Boolean phase/payload rows above, without duplicating work.
            if not accepted: continue
            physical = extend_unique(encoded,absolute)
            assert encoded.accepts(physical)
            support = sum(1 << (j-1) for j,bit in enumerate(physical[1:],1) if bit)
            assert bin(support).count("1") == encoded.variable_count//2
            supports.add(support)
            if physical[encoded.first[phase]] or physical[encoded.first[1]]:
                continue
            for a, co in projected.items():
                if not any(physical[encoded.first[pair[not v]]] for pair,v in zip(rails,a)):
                    retained = tuple(i for i,v in enumerate(sum(edges,[])) if physical[encoded.first[v]])
                    co[retained] += 1
    allmask = (1 << encoded.variable_count)-1
    assert len([a for a in supports if allmask^a in supports]) == 2
    assert len(supports)==2+len(projected)*len(tours(order))
    assert all(c==Counter({e:1 for e in tours(order)}) for c in projected.values())
    print(f"antipodal order={order} SAT_witnesses={len(projected)} "
          f"models={len(supports)} N={encoded.variable_count} degree={encoded.variable_count//2} "
          f"essential={encoded.variable_count} baseline_floor={2*encoded.variable_count-1} "
          "one antipodal pair and every retained HC coefficient checked")


def check_floor():
    """Enumerate all constant-free read-once arithmetic support dictionaries
    for up to six physical variables, canonicalizing the commutative operations."""
    @lru_cache(None)
    def polynomials(variables):
        if bin(variables).count("1")==1:
            return {frozenset((variables,))}
        out=set()
        a=(variables-1)&variables
        while a:
            b=variables^a
            if a < b:
                for left in polynomials(a):
                    for right in polynomials(b):
                        out.add(left | right)
                        out.add(frozenset(x|y for x in left for y in right))
            a=(a-1)&variables
        return out

    for d in range(1,4):
        n=2*d
        allmask=(1<<n)-1
        read_once=polynomials(allmask)
        paired={sum(1<<(2*i+int(bit)) for i,bit in enumerate(bits)) for bits in all_bits(d)}
        controls=0
        for support in read_once:
            if support <= paired and sum(allmask^a in support for a in support)==2:
                assert len(support)==2
                controls+=1
        print(f"read-once n={n} enumerated={len(read_once)} paired supports with a unique antipodal pair={controls}")


if __name__=='__main__':
    check_dual([(1,),(-1,)],1,2)
    check_dual([(1,-2)],2,2)
    check_dual([],0,3)
    check_floor()
