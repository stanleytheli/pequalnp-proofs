"""Exhaust every ordered minimum gate tree, its gate labels and its XOR count at N<=4."""
from collections import defaultdict
from functools import cache
from itertools import product

from algebraic import optimal_syntax, optimal_programs
from split_check import eval_bit, layouts


@cache
def brute(n, mask):
    low = mask & -mask
    if mask == low:
        value = sum(1 << x for x in range(1 << n) if x & low)
        return {(value, 0): 1}
    answer = defaultdict(int)
    full_word = (1 << (1 << n)) - 1
    part = (mask - 1) & mask
    while part:
        for (a, ac), an in brute(n, part).items():
            for (b, bc), bn in brute(n, mask ^ part).items():
                cells = (full_word ^ (a|b), a & ~b, ~a & b, a & b)
                for gate in (1,2,4,6,7,8,9,11,13,14):
                    table = sum(value for i, value in enumerate(cells) if gate >> i & 1)
                    answer[(table, ac+bc+(gate in (6,9)))] += an*bn
        part = (part - 1) & mask
    return dict(answer)


@cache
def tableau_tree(n, table):
    if n == 1:
        return ('leaf', 0, eval_bit(table, 0))
    for mode in range(3):
        for left, right in layouts(n):
            values = [[eval_bit(table, a | b) for b in right] for a in left]
            weights = [[f if mode==0 else 1-f if mode==1 else 1-2*f for f in row] for row in values]
            base = next(((a,b) for a in range(len(left)) for b in range(len(right)) if weights[a][b]), None)
            if base is None:
                continue
            a0, b0 = base
            if any(weights[a][b]*weights[a0][b0] != weights[a][b0]*weights[a0][b]
                   for a in range(len(left)) for b in range(len(right))):
                continue
            lt = sum(values[a][b0] << a for a in range(len(left)))
            rt = sum(values[a0][b] << b for b in range(len(right)))
            ltree = tableau_tree(len(left).bit_length()-1, lt)
            rtree = tableau_tree(len(right).bit_length()-1, rt)
            if ltree is None or rtree is None:
                return None
            gate = (8,14,9 if values[a0][b0] else 6)[mode]
            return (gate, ltree, rtree)
    return None


def brute_programs(n):
    """Choose the next ordered pair of live wires and one of ten essential binary gates."""
    full = (1 << (1 << n)) - 1
    counts = defaultdict(int)
    inputs = tuple(sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n))
    def extend(live):
        if len(live) == 1:
            counts[live[0]] += 1
            return
        for i,a in enumerate(live):
            for j,b in enumerate(live):
                if i == j:
                    continue
                rest = tuple(v for k,v in enumerate(live) if k not in (i,j))
                cells = (full ^ (a | b), a & ~b, ~a & b, a & b)
                for gate in (1,2,4,6,7,8,9,11,13,14):
                    new = sum(v for k,v in enumerate(cells) if gate >> k & 1)
                    extend(rest + (new,))
    extend(inputs)
    return counts


if __name__ == '__main__':
    for n in range(2,5):
        counts = brute(n,(1<<n)-1)
        by_table = defaultdict(dict)
        for (table, parity_gates), count in counts.items():
            by_table[table][parity_gates] = count
        programs = brute_programs(n)
        assert set(programs) == set(by_table)
        for table, empirical in by_table.items():
            tree = tableau_tree(n,table)
            count, parity = optimal_syntax(tree)
            assert empirical == {parity: count}, (n,table,empirical,count,parity)
            assert optimal_programs(tree) == programs[table]
        print(f'{n} variables: count and XOR profiles checked on {len(by_table)} functions, {sum(counts.values())} ordered tree syntaxes, {sum(programs.values())} numbered gate programs')
