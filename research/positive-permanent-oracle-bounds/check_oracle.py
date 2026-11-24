"""Exact finite controls of a shared, nested permanent-oracle flow formulation."""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
from random import Random


# Each option lists operand *occurrences*. The two copies of node 4 in a
# product and repeated positions in the matrices exercise physical gate sharing.
def assignment_options(matrix):
    return [tuple(matrix[i][j] for i, j in enumerate(p))
            for p in permutations(range(len(matrix)))
            if all(matrix[i][j] is not None for i, j in enumerate(p))]


def build():
    first = [[0, 3, 1], [1, 2, None], [3, 0, 2]]
    second = [[4, 5, None], [6, 4, 1], [5, 2, 6]]
    return [None, None, None, None, [(0,), (1,)], [(4, 4)],
            assignment_options(first), assignment_options(second), [(7, 6)], [(8,), (5,)]]


def add(a, b):
    return tuple(x+y for x,y in zip(a,b))


zero = (0, 0, 0)
leaves = [(1,0,0), (0,1,0), (0,0,1), zero]


def polynomial(options, policies):
    table = [{x: Fraction(1)} for x in leaves]
    for gate in range(len(leaves), len(options)):
        terms = defaultdict(Fraction)
        for (children, weight) in zip(options[gate], policies[gate]):
            partial = {zero: weight}
            for child in children:
                after = defaultdict(Fraction)
                for a, ca in partial.items():
                    for b, cb in table[child].items():
                        after[add(a,b)] += ca*cb
                partial = after
            for exponent, c in partial.items():
                terms[exponent] += c
        table.append(terms)
    return table[-1]


def project_flow(options, policies):
    demand = [Fraction(0)] * len(options)
    demand[-1] = Fraction(1)
    for gate in reversed(range(len(leaves), len(options))):
        for children, weight in zip(options[gate], policies[gate]):
            for child in children:
                demand[child] += demand[gate]*weight
    return tuple(demand[:3])


def dot(x,u):
    return sum(a*b for a,b in zip(x,u))


def support(options, u):
    best = list(u)+[0]
    choices = [None]*4
    for branches in options[4:]:
        values = [sum(best[j] for j in q) for q in branches]
        index = max(range(len(values)), key=values.__getitem__)
        best.append(values[index])
        choices.append([int(j==index) for j in range(len(values))])
    return best[-1], choices


def main():
    options = build()
    units = [None]*4+[[1]*len(row) for row in options[4:]]
    expanded = polynomial(options, units)
    assert all(c > 0 and c.denominator == 1 for c in expanded.values())
    dirs = list(product(range(-3,4), repeat=3))
    for u in dirs:
        h, witness = support(options, u)
        exponent = project_flow(options, witness)
        assert exponent in expanded and h == dot(exponent,u) == max(dot(a,u) for a in expanded)
    rng = Random(71439)
    for _ in range(25):
        weights = [[rng.randrange(1,9) for q in row] for row in options[4:]]
        policies = [None]*4+[[Fraction(x,sum(w)) for x in w] for w in weights]
        dist = polynomial(options, policies)
        assert sum(dist.values()) == 1 and set(dist)==set(expanded)
        expectation = tuple(sum(c*a[i] for a,c in dist.items()) for i in range(3))
        assert expectation == project_flow(options, policies)
    print(f'{len(options)} gates, 2 nested masked 3x3 permanents, {len(expanded)} output exponents.')
    print(f'{len(dirs)} support directions attained by explicit flow witnesses.')
    print('25 rational policies recovered the exact exponent mean of their full parse distributions.')


if __name__ == '__main__':
    main()
