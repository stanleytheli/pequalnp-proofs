"""Independent finite checks. Run from this directory with Python 3.10 or later."""
from functools import cache
from itertools import combinations, product
from random import Random

from recognize import AND, OR, attainable, essential_support, evaluate_circuit, evaluate_tree, recognize


def truth(n, gates):
    return tuple(evaluate_circuit(n, gates, mask) for mask in range(1 << n))


def essential(n, table):
    return all(any(table[mask] != table[mask ^ (1 << bit)] for mask in range(1 << n))
               for bit in range(n))


def restriction(table, left, right, base):
    assert base & ((1 << left) | (1 << right)) == 0
    masks = (base, base | (1 << left), base | (1 << right), base | (1 << left) | (1 << right))
    return sum(table[mask] << i for i, mask in enumerate(masks))


def boundary(n, table):
    universe = (1 << n) - 1
    minterms, zeros = [], []
    for mask, value in enumerate(table):
        if value and all(not table[mask ^ (1 << i)] for i in range(n) if mask & (1 << i)):
            minterms.append(mask)
        if not value and all(table[mask | (1 << i)] for i in range(n) if not mask & (1 << i)):
            zeros.append(universe ^ mask)
    return minterms, zeros


@cache
def read_once_tables(n, variables):
    """Enumerate monotone read-once tables using independent disjoint-variable partitions."""
    lowest = variables & -variables
    if variables == lowest:
        return {sum(1 << x for x in range(1 << n) if x & lowest)}
    results = set()
    part = (variables - 1) & variables
    while part:
        if part & lowest:
            for left in read_once_tables(n, part):
                for right in read_once_tables(n, variables ^ part):
                    results.update((left & right, left | right))
        part = (part - 1) & variables
    return results


def root_cut(n, table):
    """Necessary root condition for a read-once formula over any binary Boolean basis."""
    universe = (1 << n) - 1
    for left in range(1, universe, 2):
        right = universe ^ left
        left_masks = [mask for mask in range(1 << n) if mask & right == 0]
        right_masks = [mask for mask in range(1 << n) if mask & left == 0]
        rows = {tuple(table[a | b] for b in right_masks) for a in left_masks}
        columns = {tuple(table[a | b] for a in left_masks) for b in right_masks}
        if len(rows) <= 2 and len(columns) <= 2:
            return True
    return False


def circuit_samples(random, n):
    # Begin with a random binary tree and splice in zero to three additional gates.
    nodes = list(range(n))
    gates = []
    while len(nodes) > 1:
        left, right = random.sample(nodes, 2)
        nodes.remove(left)
        nodes.remove(right)
        gates.append((random.choice(('and', 'or')), left, right))
        nodes.append(n + len(gates) - 1)
    for _ in range(random.randrange(4)):
        position = random.randrange(len(gates))
        wire = n + position
        operation, left, right = gates[position]
        other = random.randrange(wire)
        if random.randrange(2):
            left, right = right, left
        revised = [(op, a + (a >= wire), b + (b >= wire)) for op, a, b in gates[position + 1:]]
        gates = (gates[:position] + [(random.choice(('and', 'or')), left, other),
                                     (operation, wire, right)] + revised)
    return gates


def circuit_checks():
    random = Random(1342997)
    candidate_count = exact_count = pair_count = intersection_count = 0
    for n in range(2, 7):
        oracle = read_once_tables(n, (1 << n) - 1)
        for _ in range(120):
            gates = circuit_samples(random, n)
            table = truth(n, gates)
            for first, second in combinations(range(n), 2):
                valid_mask = (1 << first) | (1 << second)
                expected = {restriction(table, first, second, base) for base in range(1 << n)
                            if base & valid_mask == 0}
                returned = attainable(n, gates, first, second)
                assert set(returned) == expected
                for word, base in returned.items():
                    assert restriction(table, first, second, base) == word
                pair_count += 1
            actual_support = {i for i in range(n) if any(table[x] != table[x ^ (1 << i)]
                                                         for x in range(1 << n))}
            assert essential_support(n, gates) == actual_support
            if not essential(n, table):
                continue
            candidate_count += 1
            minterms, zeros = boundary(n, table)
            for minterm, zero_set in product(minterms, zeros):
                assert (minterm & zero_set).bit_count() <= len(gates) - n + 2
                intersection_count += 1
            answer, witness = recognize(n, gates)
            table_word = sum(value << i for i, value in enumerate(table))
            assert answer == (table_word in oracle)
            if answer:
                assert table == tuple(evaluate_tree(witness, mask) for mask in range(1 << n))
                exact_count += 1
            else:
                a, b, conjunction, disjunction = witness
                assert restriction(table, a, b, conjunction) == AND
                assert restriction(table, a, b, disjunction) == OR
    print(f'600 trimmed circuits and complete semantic support checks; {candidate_count} all-essential; {exact_count} read-once')
    print(f'{pair_count} cofactor sets with every returned background tested; '
          f'{intersection_count} minterm/zero-certificate bounds')


def fold(n, gates, op, leaves):
    result = leaves[0]
    for other in leaves[1:]:
        gates.append((op, result, other))
        result = n + len(gates) - 1
    return result


def spike_checks():
    targets = 0
    for sizes in ((2, 2), (3, 2), (2, 2, 2), (3, 3), (4, 3), (3, 2, 3), (3, 3, 3)):
        starts = [sum(sizes[:i]) for i in range(len(sizes))]
        n = sum(sizes)
        blocks = [list(range(start, start + size)) for start, size in zip(starts, sizes)]
        baseline = tuple(int(any(all(mask & (1 << i) for i in block) for block in blocks))
                         for mask in range(1 << n))
        for omitted in product(*blocks):
            gates = []
            selected = [[i for i in block if i != c] for block, c in zip(blocks, omitted)]
            ys = [fold(n, gates, 'and', part) for part in selected]
            other_conjunction = fold(n, gates, 'and', ys[1:])
            lifted = fold(n, gates, 'or', [omitted[0], other_conjunction])
            products = [fold(n, gates, 'and', [ys[0], lifted])]
            products += [fold(n, gates, 'and', [y, c]) for y, c in zip(ys[1:], omitted[1:])]
            fold(n, gates, 'or', products)
            assert len(gates) == n + len(sizes) - 2
            table = truth(n, gates)
            spike = sum(1 << i for part in selected for i in part)
            transversal = sum(1 << part[0] for part in selected)
            assert [mask for mask in range(1 << n) if table[mask] != baseline[mask]] == [spike]
            minterms, zeros = boundary(n, table)
            assert spike in minterms and transversal in zeros and essential(n, table)
            assert (spike & transversal).bit_count() == len(sizes)
            assert max((a & b).bit_count() for a, b in product(minterms, zeros)) == len(sizes)
            targets += 1
    noncuts = 0
    for n in range(3, 8):
        for point in range(1 << n):
            table = tuple((mask.bit_count() % 2) ^ (mask == point) for mask in range(1 << n))
            assert essential(n, table) and not root_cut(n, table)
            noncuts += 1
    path = tuple(int(bool((x & 3 == 3) or (x & 12 == 12) or (x & 5 == 5))) for x in range(16))
    assert not root_cut(4, path)
    print(f'{targets} exact-size monotone spike circuits, including full truth tables and overlaps')
    print(f'{noncuts} ordinary parity-flip functions and P4 tested on every possible binary root cut')


def reduction_checks():
    random = Random(20261123)
    count = 0
    for n in range(1, 7):
        for _ in range(30):
            clauses = [random.sample(range(2*n), random.randrange(1, min(3, 2*n)+1))
                       for _ in range(random.randrange(1, 8))]
            def satisfies(bits):
                return all(any(bits & (1 << lit) for lit in clause) for clause in clauses)
            full_rails = [sum(1 << (2*i + ((x >> i) & 1)) for i in range(n)) for x in range(1 << n)]
            consistent = [x for x in range(1 << (2*n)) if all((x >> (2*i)) & 3 != 3 for i in range(n))]
            num_sat = sum(satisfies(x) for x in full_rails)
            assert bool(num_sat) == any(satisfies(x) for x in consistent)
            false_positives = [x for x in consistent if satisfies(x) and
                               all((x >> (2*i)) & 3 for i in range(n))]
            assert len(false_positives) == num_sat
            count += 1
    print(f'{count} sparse-formula controls for satisfiability and parsimonious boundary discrepancy')


if __name__ == '__main__':
    circuit_checks()
    spike_checks()
    reduction_checks()
