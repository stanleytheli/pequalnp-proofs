"""Exhaustive normalized Boolean-subalgebra recognition through four pairs."""
from itertools import permutations
from functools import lru_cache


def block_families(d):
    """Generate supports from literal read-once block factorizations."""
    partitions = {()}
    for i in range(d):
        partitions = {
            parts for partition in partitions for parts in
            [(*partition,(i,)), *(partition[:j]+(partition[j]+(i,),)+partition[j+1:]
                                  for j in range(len(partition)))]
        }
    out = set()
    for part in partitions:
        masks = [sum(1<<i for i in group) for group in part]
        block_unions = {0}
        for mask in masks:
            block_unions |= {u|mask for u in block_unions}
        for base in range(1<<d):
            out.add(sum(1<<(u^base) for u in block_unions))
    return out


def subalgebra(array, d):
    base = (array & -array).bit_length()-1
    normalized = {(x^base) for x in range(1<<d) if (array >> x)&1}
    full = (1<<d)-1
    return (all(full^u in normalized for u in normalized) and
            all(u&v in normalized for u in normalized for v in normalized))


def physical_read_once(d):
    n=2*d
    @lru_cache(None)
    def expressions(bits):
        if bits & (bits-1)==0:
            return {frozenset([bits])}
        out=set()
        left=(bits-1)&bits
        while left:
            right = bits^left
            if left < right:
                for a in expressions(left):
                    for b in expressions(right):
                        out.add(a|b)
                        out.add(frozenset(x|y for x in a for y in b))
            left=(left-1)&bits
        return out
    paired = {sum(1<<(2*i+((x>>i)&1)) for i in range(d)): x for x in range(1<<d)}
    return {sum(1<<paired[t] for t in family) for family in expressions((1<<n)-1) if family <= paired.keys()}


if __name__ == "__main__":
    for d in range(1,5):
        modes=1<<d
        expected=block_families(d)
        if d<=3:
            assert expected==physical_read_once(d)
        checked=0
        for f in range(1,1<<modes):
            inputs=[i for i in range(modes) if (f>>i)&1]
            essential=all(any((i>>j)&1 for i in inputs) and any(not ((i>>j)&1) for i in inputs)
                          for j in range(d))
            if essential:
                assert subalgebra(f,d) == (f in expected)
                checked += 1
        print(f"{d} pairs: all {checked} fully essential support families tested; {len(expected)} at the floor")
