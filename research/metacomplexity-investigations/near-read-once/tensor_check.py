"""Compare every good Boolean matrix partition with tensor factors on <=4 inputs."""
from functools import cache
from itertools import combinations, product

from split_check import masks_on


@cache
def grids(n, mode):
    table = {}
    for word in range(1 << (1 << n)):
        values = []
        for z in product((0, 1, 2), repeat=n):
            total = 0
            for x in range(1 << n):
                raw = (word >> x) & 1
                bit = raw if mode == 0 else 1-raw if mode == 1 else 1-2*raw
                for i, value in enumerate(z):
                    bit *= value if (x >> i) & 1 else 1-value
                total += bit
            values.append(total)
        table[word] = values
    return table


def all_splits(n):
    full = (1 << n) - 1
    edges = list(combinations(range(n), 2))
    partitions = list(range(1, full, 2))
    partition_masks = [(masks_on(left), masks_on(full ^ left)) for left in partitions]
    crossings = [sum(1 << k for k, (i,j) in enumerate(edges) if ((left >> i) ^ (left >> j)) & 1)
                 for left in partitions]
    project = []
    for i, j in edges:
        free = masks_on(full ^ (1 << i) ^ (1 << j))
        project.append([[x | (a << i) | (b << j) for x in free] for a, b in product((0,1),repeat=2)])
    control = targets = 0
    for table in range(1 << (1 << n)):
        bit = tuple(table >> k & 1 for k in range(1 << n))
        if any(all(bit[x] == bit[x ^ (1 << i)] for x in range(1 << n)) for i in range(n)):
            continue
        targets += 1
        factors = [0,0,0]
        for k, pattern in enumerate(project):
            words = [sum(bit[x] << h for h, x in enumerate(fiber)) for fiber in pattern]
            for mode in range(3):
                vector = grids(n-2,mode)
                a, b, c, d = (vector[word] for word in words)
                if any(a0*d0 != b0*c0 for a0,b0,c0,d0 in zip(a,b,c,d)):
                    factors[mode] |= 1 << k
        for cross, (left, right) in zip(crossings,partition_masks):
            expected_rows = [tuple(bit[l | r] for r in right) for l in left]
            expected = len(set(expected_rows)) <= 2 and len(set(zip(*expected_rows))) <= 2
            found = any(not(g & cross) for g in factors)
            assert found == expected, (n, table, cross, factors)
            control += 1
    print(f'{n} variables: {control} matrix-cut versus tensor-factor checks across {targets} essential functions')


if __name__ == '__main__':
    for n in range(2, 5):
        all_splits(n)
