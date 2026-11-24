"""Check physical restrictions and rational coefficient bounds for symmetric flag statistics."""
from fractions import Fraction
from itertools import combinations, product
from math import comb
from random import Random


def flag(bits):
    return any(a and b for a, b in zip(bits, bits[1:]))


def local_tables(length):
    count = 0
    for inner in range(1 << (length-1)):
        side = [0] + [(inner >> i) & 1 for i in range(length-1)] + [1]
        k = next(i for i in range(length) if side[i] != side[i+1])
        for x, y in product([0, 1], repeat=2):
            bits = [0] * (length+1)
            bits[k], bits[k+1] = (x, y) if side[k] == 0 else (y, x)
            assert flag(bits) == (x and y)
            bits = [0] * (length+1)
            bits[0], bits[-1] = x, y
            bits[1], bits[-2] = 1, 1
            assert flag(bits) == (x or y)
        count += 1
    return count


def rational_interpolation():
    rng = Random(8743)
    count = 0
    for g in range(2, 29):
        for d in range(1, min(g, 8)+1):
            step = g // d
            values = [Fraction(rng.randint(-2, 2)) for _ in range(d+1)]
            def q(w):
                total = 0
                for j in range(d+1):
                    term = values[j]
                    for i in range(d+1):
                        if i != j:
                            term *= Fraction(w-i*step, (j-i)*step)
                    total += term
                return total
            # The denominator estimate only needs |q|≤2 at the interpolation nodes.
            diff = [q(i) for i in range(g+1)]
            mass = 0
            for j in range(g+1):
                assert j <= d or diff[0] == 0
                mass += abs(diff[0]) * comb(g, j)
                diff = [b-a for a,b in zip(diff, diff[1:])]
            assert mass <= 2 * 22**d
            count += 1
    return count


def shifted_patterns():
    results = 0
    for reflected, t in product([False, True], [1, 2, 3]):
        g = 8*t+1
        for transition in range((g-1)//2+1):
            offset = max(0, transition-t//2)
            assert 0 <= offset <= g-4*t
            # The XOR choice can select any t-bit pattern including its complement.
            for z in product([0,1], repeat=2*t):
                first = [digit for bit in z for digit in (bit, 1-bit)]
                for choices in product(range(4), repeat=t):
                    second = [int(i == choice) for choice in choices for i in range(4)]
                    weight = sum(z[2*j+c//2] ^ (c%2) for j,c in enumerate(choices))
                    if reflected:
                        total = g-4*t-offset + sum((not a) or (not b) for a,b in zip(first,second))
                        assert total == g-offset-weight
                    else:
                        assert offset + sum(a and b for a,b in zip(first,second)) == offset+weight
                    results += 1
    return results


if __name__ == '__main__':
    cuts = sum(local_tables(i) for i in range(10, 14))
    print(f'{cuts} endpoint-separated binary cuts, exact physical AND/OR restrictions for all four bit pairs')
    print(f'{rational_interpolation()} rational interpolation and multilinear coefficient-mass controls')
    print(f'{shifted_patterns()} shifted and reflected pattern embeddings checked')
