"""Exhaust the graph-plus-long-term construction against the source CNF."""
from itertools import combinations, product
import random


def optimal(n, clauses):
    masks = set()
    sat_count = 0
    for bits in product((False,True),repeat=n):
        satisfied = sum(1 << j for j,clause in enumerate(clauses)
                        if any(bits[abs(l)-1] == (l>0) for l in clause))
        masks.add(satisfied)
        if satisfied == (1 << len(clauses))-1:
            sat_count += 1
    return masks, sat_count


def subsets(s):
    h = s
    while True:
        yield h
        if not h:
            return
        h = (h-1)&s


def analyze(n,clauses):
    m = len(clauses)
    s = ((1 << m)-1) << (2*n)
    terms = {3 << (2*i) for i in range(n)}
    for j,clause in enumerate(clauses):
        for l in clause:
            idx = 2*(abs(l)-1) + int(l<0)
            terms.add((1 << idx) | (1 << (2*n+j)))
    terms.add(s)
    # A top-level minimal zero certificate is an inclusion-minimal
    # hitting set of the actual DNF terms.
    zero = []
    for z in range(1 << (2*n+m)):
        private = 0
        for term in terms:
            intersection = z&term
            if not intersection:
                break
            if intersection&(intersection-1) == 0:
                private |= intersection
        else:
            if private == z:
                zero.append(z)
    sat, full = optimal(n,clauses)
    overlap = max(bin(z&term).count("1") for z in zero for term in terms)
    best = max(bin(a).count("1") for a in sat)
    if best >= 2:
        assert best == overlap
    assert sum((z&s)==s for z in zero) == full
    requests = set().union(*(set(subsets(mask)) for mask in sat))
    realized = set().union(*(set(subsets((z&s) >> (2*n))) for z in zero))
    assert realized == requests
    return len(zero),len(requests)


def main():
    rng = random.Random(151)
    instances = []
    base = [(1,),(-1,),(2,),(-2,),(1,2),(-1,2),(1,-2),(-1,-2)]
    instances.extend((2,c) for c in combinations(base,3))
    instances.extend((2,c) for c in combinations(base,4))
    for _ in range(140):
        n = rng.randrange(2,5)
        clauses = []
        for _ in range(rng.randrange(3,7)):
            variables = rng.sample(range(1,n+1),rng.randrange(1,min(3,n)+1))
            clauses.append(tuple(i*rng.choice((-1,1)) for i in variables))
        instances.append((n,clauses))
    total_z = total_requests = 0
    for n,clauses in instances:
        z,requests = analyze(n,clauses)
        total_z += z
        total_requests += requests
    print(f"{len(instances)} source CNFs; {total_z} minimal zero certificates; "
          f"{total_requests} feasible clause subsets. All MaxSAT optima and full-overlap counts matched.")


if __name__ == "__main__":
    main()
