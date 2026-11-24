"""Small exact controls for the two uniform reductions in succinct_gap.py."""
from collections import Counter
from itertools import permutations, product
from math import factorial

from succinct_gap import Circuit, bounded_occurrence, planted, signed_transfer, truth


def all_bits(n):
    return product((False, True), repeat=n)


def sat(clauses, bits):
    return all(any(truth([False, *bits], lit) for lit in clause) for clause in clauses)


def tours(order):
    result = set()
    for tail in permutations(range(1, order)):
        cycle = (0, *tail)
        result.add(tuple(sorted(i*order+j for i, j in zip(cycle, cycle[1:]+cycle[:1]))))
    assert len(result) == factorial(order-1)
    return result


def check_network(clauses, bits, order, exhaustive):
    circuit, bounded, rails, edges, output = planted(clauses, bits, order)
    baseline = bounded.representative[1]
    assert baseline > 0
    occurrences = bounded.occurrences()
    assert max(occurrences.values()) <= 3
    assert max(map(len, bounded.clauses)) <= 3
    assert len(occurrences) == len(bounded.signed_copies)-1
    good = tours(order)
    models = list(a for a in all_bits(bits) if sat(clauses, a))
    target_coefficients = {a: Counter() for a in models}
    baseline_count = 0
    accepted_count = 0
    primary_tests = 0
    if exhaustive:
        primaries = all_bits(circuit.primary_count)
    else:
        # Check all primary SAT-rail settings and *all* selected tour masks.
        # The cycle checker was separately exhausted for every 3x3 edge mask.
        primaries = ((flag, *rails_here, *[i in cycle for i in range(order**2)])
                     for flag in (False, True) for rails_here in all_bits(bits*2)
                     for cycle in ((), *good))
    for primary in primaries:
        original = circuit.evaluate(primary)
        edge_indices = tuple(i for i, v in enumerate(sum(edges, [])) if original[v])
        assigned = tuple(original[q] for _, q in rails)
        one_rail = all(original[p] != original[q] for p, q in rails)
        is_base = primary[0] and not any(primary[1:])
        is_hard = not primary[0] and one_rail and sat(clauses, assigned) and edge_indices in good
        assert original[output] == (is_base or is_hard)
        primary_tests += 1
        extended = bounded.extend(original)
        assert bounded.accepts(extended) == (is_base or is_hard)
        if not (is_base or is_hard):
            continue
        accepted_count += 1
        if is_base:
            assert [i for i, b in enumerate(extended) if b] == [baseline]
            baseline_count += 1
        else:
            assert not extended[baseline]
            for witness, coefficients in target_coefficients.items():
                # In the literal projection, any selected wrong rail annihilates
                # this monomial, and all nondistinguished copies map to one.
                if not any(extended[bounded.representative[pair[not bit]]]
                           for pair, bit in zip(rails, witness)):
                    retained = tuple(i for i, v in enumerate(sum(edges, []))
                                     if extended[bounded.representative[v]])
                    coefficients[retained] += 1
    assert baseline_count == 1
    assert accepted_count == 1+len(models)*len(good)
    assert all(coef == Counter({tour: 1 for tour in good}) for coef in target_coefficients.values())
    print(f"planted m={order} witness_bits={bits} sat_count={len(models)} "
          f"primaries_checked={primary_tests} accepted={accepted_count} "
          f"exponent_bits={len(occurrences)} clauses={len(bounded.clauses)} max_occurrence=3")


def check_signed(pos, neg, psize, nsize, order):
    circuit, bounded, flags, p, n, edges, output = signed_transfer(pos, neg, psize, nsize, order)
    assert max(bounded.occurrences().values()) <= 3
    assert max(map(len, bounded.clauses)) <= 3
    coefficients = Counter()
    for setting in all_bits(circuit.primary_count):
        original = circuit.evaluate(setting)
        extended = bounded.extend(original)
        assert bounded.accepts(extended) == original[output]
        if not original[output]:
            continue
        idx = tuple(i for i, v in enumerate(sum(edges, [])) if extended[bounded.representative[v]])
        sign = -1 if extended[bounded.representative[flags[2]]] else 1
        coefficients[idx] += sign
    answer = Counter({idx: 1 for idx in tours(order)})
    difference = sum(sat(pos, a) for a in all_bits(psize)) - sum(sat(neg, a) for a in all_bits(nsize))
    answer[()] += difference
    assert coefficients == answer
    print(f"signed m={order} primaries_checked={2**circuit.primary_count} constant={difference} "
          f"cycle_monomials={len(tours(order))} max_occurrence=3")


def check_local_parsimony():
    for op in ("and", "or"):
        for sa, sb in product((-1, 1), repeat=2):
            c = Circuit(2)
            out = c.gate(op, sa, 2*sb)
            definitional = c.clauses(out)[:-1]
            for x, y, z in all_bits(3):
                lhs = all(any(truth([False, x, y, z], lit) for lit in cl) for cl in definitional)
                assert lhs == (z == c.evaluate([x, y])[out])
    for n in range(1, 9):
        for baseline in (False, True):
            enc = bounded_occurrence([(1,)]*n, [False, baseline], [1])
            models = [[False, *bits] for bits in all_bits(n)]
            # Drop all unit clauses; only the signed implication cycle remains.
            chain = enc.clauses[n:]
            solutions = [x for x in models if all(any(truth(x, l) for l in cl) for cl in chain)]
            assert solutions == [enc.extend([False, False]), enc.extend([False, True])]
    print("functional Tseitin gate controls and signed equality cycles of lengths 1 through 8 passed")


if __name__ == "__main__":
    check_local_parsimony()
    check_network([(1,), (-1,)], 1, 2, True)
    check_network([(1, -2)], 2, 2, True)
    check_network([], 0, 3, True)
    check_network([(1, -2)], 2, 3, False)
    check_signed([(1,)], [(-1,)], 1, 1, 2)
    check_signed([], [(1,), (-1,)], 1, 1, 2)
    check_signed([(1,), (-1,)], [], 1, 1, 2)
