"""Exact control for the graph-independent literal coupling of edge events."""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from random import Random


def on(label, bits):
    if label == 0:
        return True
    return bits[abs(label)-1] == (label>0)


def check():
    rng = Random(47600)
    checks = 0
    for _ in range(12):
        n, count = 3, 4
        opts = []
        for v in range(count):
            literals = [0]+[(i+1)*rng.choice((-1,1)) for i in range(n)]
            weights = [rng.randrange(3) for _ in literals]+[1]
            den = sum(weights)
            opts.append([(literal, Fraction(a, den)) for literal, a in zip(literals+[None], weights) if a])
        edges = [(u, v) for u in range(count) for v in range(u+1, count) if rng.randrange(3)]
        masses = defaultdict(Fraction)
        for outcome in product(*opts):
            labels = [label for label, _ in outcome]
            prob = Fraction(1)
            for _, a in outcome:
                prob *= a
            terms = set()
            for u, v in edges:
                if labels[u] is None or labels[v] is None:
                    continue
                term = frozenset({labels[u],labels[v]}-{0})
                if all(-i not in term for i in term):
                    terms.add(term)
            for term in terms:
                masses[term] += prob
        for bits in product((False, True), repeat=n):
            probabilities = [sum(a for label, a in row if label is not None and on(label,bits))
                             for row in opts]
            actual = Fraction(0)
            for spins in product((False, True), repeat=count):
                if not any(spins[u] and spins[v] for u, v in edges):
                    continue
                p = Fraction(1)
                for w, picked in zip(probabilities, spins):
                    p *= w if picked else 1-w
                actual += p
            active = [a for term, a in masses.items() if all(on(i,bits) for i in term)]
            assert max(active, default=0) <= actual <= sum(active)
            assert sum(active) <= (2*n+1)**2 * max(active, default=0)
            checks += 1
    print(f"{checks} exact input-independent literal-coupling bounds passed")


if __name__ == '__main__':
    check()
