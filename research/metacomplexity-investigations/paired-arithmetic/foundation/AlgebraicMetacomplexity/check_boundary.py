"""Check the two-occurrence elimination and the exact-three uniqueness boundary."""
from collections import Counter
from itertools import combinations, product
from random import Random

from check_gap import all_bits, sat


def twice_sat(clauses, restriction=None):
    clauses = [set(c) for c in clauses]
    if restriction is not None:
        clauses = [c-{-restriction} for c in clauses if restriction not in c]
    clauses = [c for c in clauses if not any(-l in c for l in c)]
    while clauses:
        if any(not c for c in clauses):
            return False
        variable = abs(next(iter(clauses[0])))
        pos = [c for c in clauses if variable in c]
        neg = [c for c in clauses if -variable in c]
        assert len(pos)+len(neg) <= 2
        clauses = [c for c in clauses if variable not in c and -variable not in c]
        if pos and neg:
            resolvent = (pos[0]-{variable}) | (neg[0]-{-variable})
            if not any(-l in resolvent for l in resolvent):
                clauses.append(resolvent)
    return True


def check_elimination():
    rng = Random(71237)
    tests = 0
    for n in range(1, 8):
        for _ in range(200):
            pool = list(range(1, n+1))*2
            rng.shuffle(pool)
            formula = []
            while pool:
                width = rng.randint(1, min(6, len(pool)))
                formula.append([pool.pop()*rng.choice((-1, 1)) for _ in range(width)])
            if rng.randrange(8) == 0:
                formula.append([])
            models = [a for a in all_bits(n) if sat(formula, a)]
            assert twice_sat(formula) == bool(models)
            for i in range(1, n+1):
                for sign in (-1, 1):
                    assert twice_sat(formula, sign*i) == any(a[i-1] == (sign == 1) for a in models)
                    tests += 1
    print(f"two-occurrence satisfiability compared with enumeration on 1400 formulas and {tests} single-bit restrictions")


def check_exact_three():
    seen = 0
    for n in (3, 4):
        clauses = [tuple(x*s for x,s in zip(triplet, signs)) for triplet in combinations(range(1, n+1), 3)
                   for signs in product((-1, 1), repeat=3)]
        for m in range(0, n+1):
            for formula in combinations(clauses, m):
                occurrences = Counter(abs(l) for c in formula for l in c)
                if max(occurrences.values(), default=0) > 3:
                    continue
                models = sum(sat(formula, a) for a in all_bits(n))
                assert models >= 2
                seen += 1
    print(f"checked all {seen} three-/four-variable exact-three formulas with distinct literals and occurrence ≤3, omitting repeated clauses")


if __name__ == "__main__":
    check_elimination()
    check_exact_three()
