"""Evaluate the signed-literal markers of the nonuniform-language construction."""
from fractions import Fraction
from itertools import product
from positive_odd import physical, records
from check_positive_odd import physical_coefficient


def literal(value, bit):
    return value if bit else 1-value


def check():
    tests = []
    for n, data, clauses in [(1, 1, []), (1, 1, [(1,)]), (1, 1, [(-1,)]),
                              (1, 1, [(1,), (-1,)]), (2, 1, []),
                              (2, 1, [(1,)]), (2, 1, [(-2,)]), (2, 2, [(1,), (-2,)])]:
        g, k = records(n, clauses, {i: (i, True) for i in range(1, data+1)},
                       {i: (i, False) for i in range(1, data+1)})
        obj = physical(g, k)
        for input_bits in product((Fraction(0), Fraction(1), Fraction(1, 3)), repeat=data):
            labels = {(i+1, bit): literal(x, bit) for i, x in enumerate(input_bits)
                      for bit in (False, True)}
            direct = Fraction(0)
            for assignment in product((False, True), repeat=n):
                if not all(any(assignment[abs(j)-1] == (j>0) for j in c) for c in clauses):
                    continue
                weight = Fraction(1)
                for i, x in enumerate(input_bits):
                    weight *= literal(x, assignment[i])
                direct += weight
            evaluated = physical_coefficient(obj, labels)
            assert direct == evaluated
            tests.append((direct, tuple(input_bits)))
    print(f"{len(tests)} independent physical-root contractions with paired markers passed, "
          f"including {sum(a == 0 for a, _ in tests)} zeroes and witness multiplicity "
          f"{int(max(a for a, _ in tests))}")


if __name__ == '__main__':
    check()
