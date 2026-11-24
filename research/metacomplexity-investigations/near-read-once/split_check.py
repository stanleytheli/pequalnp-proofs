"""Truth-table checks of arbitrary binary read-once decomposition, with N<=4."""
from functools import cache
from itertools import product


def masks_on(mask):
    bits = [i for i in range(mask.bit_length()) if mask >> i & 1]
    return [sum(bit << i for bit, i in zip(choice, bits)) for choice in product((0, 1), repeat=len(bits))]


def eval_bit(table, assignment):
    return table >> assignment & 1


@cache
def layouts(n):
    full = (1 << n) - 1
    return [(masks_on(a), masks_on(full ^ a)) for a in range(1, full, 2)]


@cache
def accepts(n, table):
    if n == 1:
        return table in (1, 2)  # child may be a signed literal
    for left, right in layouts(n):
        rows = [tuple(eval_bit(table, l | r) for r in right) for l in left]
        if len(set(rows)) != 2:
            continue
        columns = list(zip(*rows))
        if len(set(columns)) != 2:
            continue
        col = next(c for c in columns if len(set(c)) == 2)
        row = next(r for r in rows if len(set(r)) == 2)
        # The ordering of masks defines a permutation of the new variable positions.
        left_table = sum(bit << i for i, bit in enumerate(col))
        right_table = sum(bit << i for i, bit in enumerate(row))
        return accepts(len(left).bit_length()-1, left_table) and accepts(len(right).bit_length()-1, right_table)
    return False


@cache
def formula_tables(n, mask):
    low = mask & -mask
    full_word = (1 << (1 << n)) - 1
    if mask == low:
        v = sum(1 << x for x in range(1 << n) if x & low)
        return {v, full_word ^ v}
    answers = set()
    part = (mask - 1) & mask
    while part:
        if part & low:
            for a, b in product(formula_tables(n, part), formula_tables(n, mask ^ part)):
                entries = (full_word ^ (a | b), a & ~b, ~a & b, a & b)
                for gate in (1, 2, 4, 6, 7, 8, 9, 11, 13, 14):
                    answers.add(sum(entry for i, entry in enumerate(entries) if gate >> i & 1))
        part = (part - 1) & mask
    return answers


if __name__ == '__main__':
    for n in range(2, 5):
        yes = formula_tables(n, (1 << n) - 1)
        essential = read_once = 0
        for table in range(1 << (1 << n)):
            if any(all(eval_bit(table, x) == eval_bit(table, x ^ (1 << i)) for x in range(1 << n))
                   for i in range(n)):
                continue
            essential += 1
            result = accepts(n, table)
            assert result == (table in yes), (n, table, result)
            read_once += result
        print(f'{n} variables: {essential} all-essential arbitrary truth tables, {read_once} read-once')
