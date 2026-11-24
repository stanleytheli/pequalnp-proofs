"""Controls for exact unsigned and fixed-characteristic transfer tests."""
from collections import Counter
from itertools import permutations
from math import factorial

from check_gap import all_bits, sat, tours
from succinct_gap import unsigned_fibers


def check(clauses, index_bits, witness_bits, m, baseline):
    circuit, encoded, flag, witness, edges, index_vars, out = unsigned_fibers(
        clauses, index_bits, witness_bits, m, baseline)
    assert max(encoded.occurrences().values()) <= 3 and max(map(len, encoded.clauses)) <= 3
    counts, observed = Counter(), set()
    representatives = []
    for tail in permutations(range(1, m)):
        tour = (0, *tail)
        mask = tuple(sorted(i*m+j for i, j in zip(tour, tour[1:]+tour[:1])))
        index = tuple(tour.index(2*i+1) < tour.index(2*i+2) for i in range(index_bits))
        representatives.append((mask, index))
        observed.add(index)
    assert observed == set(all_bits(index_bits))
    for mask, index in representatives:
        for choice in (False, True):
            for w in all_bits(witness_bits):
                values = circuit.evaluate([choice, *w, *[j in mask for j in range(m*m)]])
                extended = encoded.extend(values)
                assert tuple(values[v] for v in index_vars) == index
                accept = (choice and baseline and not any(w)) or (not choice and sat(clauses, index+w))
                assert values[out] == encoded.accepts(extended) == accept
                if accept:
                    kept = tuple(j for j, v in enumerate(sum(edges, []))
                                 if extended[encoded.representative[v]])
                    assert kept == mask
                    counts[mask] += 1
        assert counts[mask] == int(baseline) + sum(sat(clauses, index+w) for w in all_bits(witness_bits))
    exact = all(counts[mask] == 1 for mask in tours(m))
    modular = [p for p in (2, 3, 5) if all(counts[mask] % p == 1 for mask in tours(m))]
    print(f"fiber m={m} tours={factorial(m-1)} index_bits={index_bits} witnesses={witness_bits} "
          f"baseline={baseline} coefficient_range={min(counts[mask] for mask in tours(m))}.."
          f"{max(counts[mask] for mask in tours(m))} identity_Q={exact} identity_mod={modular} "
          f"cases={2*factorial(m-1)*2**witness_bits}")


if __name__ == "__main__":
    check([(-1, 3), (1, -3)], 2, 1, 5, False)
    check([(1, 2)], 2, 0, 5, False)
    check([], 1, 1, 3, True)
    check([(2, 3)], 1, 2, 3, True)
    check([(1, 2)], 1, 1, 3, True)
