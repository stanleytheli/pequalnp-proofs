"""Exact controls for two matching faces, signed affine slopes, and recovery of the initial form."""
from fractions import Fraction
from itertools import permutations, product
from math import prod
from random import Random


def add(p, q):
    result = dict(p)
    for exp, value in q.items():
        result[exp] = result.get(exp, 0)+value
        if not result[exp]:
            del result[exp]
    return result


def multiply(p, q):
    result = {}
    for a, x in p.items():
        for b, y in q.items():
            exp = tuple(i+j for i,j in zip(a,b))
            result[exp] = result.get(exp, 0)+x*y
    return {exp:val for exp,val in result.items() if val}


def forms():
    one, x, y, z = (0,0,0), (1,0,0), (0,1,0), (0,0,1)
    # Every form is nonnegative on the unit cube, with value exactly one at the midpoint.
    return [{one:1}, {x:2}, {y:1,z:1}, {one:2,x:-2}, {one:1,x:1,y:-1},
            {one:Fraction(3,2),z:-1}, {x:Fraction(1,2),z:Fraction(3,2)}]


def initial(p):
    degree = min(sum(e) for e in p)
    return {e : v for e,v in p.items() if sum(e)==degree}


def edges(p):
    return tuple(enumerate(p))


def total_match_cost(M, table):
    return tuple(sum(table[e][j] for e in M) for j in [0,1])


def poly_for(M, table, weight):
    ans = {(0,0,0):weight}
    for e in M:
        ans = multiply(ans,table[e])
    return ans


def run():
    rng = Random(59003)
    controls = diverse = zeros = 0
    counts = [0]*7
    for k in range(1,7):
        all_m = [edges(p) for p in permutations(range(k))]
        for case in range(31):
            grid = list(product(range(k),repeat=2))
            available = {e for e in grid if rng.randrange(6)>0}
            avail = [M for M in all_m if all(e in available for e in M)]
            if not avail:
                zeros += 1
                continue
            # Lexicographic scales model exp(-b/t)*t^a, including negative exponents.
            costs = {e: (rng.randrange(3) if case%3 else 0, rng.randrange(3)-1 if case%4 else 0) for e in grid}
            amp = {e:Fraction(rng.randint(1,4),rng.randint(1,3)) for e in grid}
            form = {e:rng.choice(forms()) for e in grid}
            best = min(total_match_cost(M,costs) for M in avail)
            good = [M for M in avail if total_match_cost(M,costs)==best]
            support = set().union(*map(set,good))
            assert good == [M for M in all_m if all(e in support for e in M)]
            if len(good)>1:
                diverse += 1
            full = {}
            for M in good:
                full = add(full,poly_for(M, form, prod(amp[e] for e in M)))
            unit = (0,0,0)
            lowest = min(sum(unit not in form[e] for e in M) for M in good)
            minima = [M for M in good if sum(unit not in form[e] for e in M)==lowest]
            keep = set().union(*map(set,minima))
            predicted = {}
            retained = [M for M in all_m if all(e in keep for e in M)]
            assert retained == minima
            for M in retained:
                labels = {e:initial(form[e]) for e in M}
                predicted = add(predicted,poly_for(M,labels,prod(amp[e] for e in M)))
            assert predicted == initial(full)
            assert all(v>0 for v in predicted.values())
            controls += 1
            counts[k] += len(avail)
    print(f'{controls} nonzero matrices and {zeros} structural zeros, through order six')
    print(f'{diverse} cases with multiple good permutations, {sum(counts)} admissible matchings enumerated')
    print('Both matching faces and every coefficient of the recovered initial polynomial agreed exactly.')


if __name__=='__main__':
    run()
