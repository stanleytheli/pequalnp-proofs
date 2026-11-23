"""Compare the even-component quotient with the direct path-cover objective."""
from itertools import combinations, product


def quotient(n, odd, even):
    neighbors = [set() for _ in range(n)]
    for a, b in even:
        neighbors[a].add(b)
        neighbors[b].add(a)
    owner = [-1] * n
    components = []
    for start in range(n):
        if owner[start] >= 0:
            continue
        index = len(components)
        owner[start] = index
        component = [start]
        for v in component:
            for w in neighbors[v]:
                if owner[w] < 0:
                    component.append(w)
                    owner[w] = index
        components.append(component)
    free = set()
    offset = 0
    for i, comp in enumerate(components):
        edges = sum(len(neighbors[v]) for v in comp) // 2
        offset += min(len(comp), edges)
        if edges >= len(comp):
            free.add(i)
    pairs = {(owner[a], owner[b]) for a, b in odd if owner[a] not in free and owner[b] not in free}
    return offset + min(mask.bit_count() for mask in range(1 << len(components))
                        if all(mask >> a & 1 or mask >> b & 1 for a, b in pairs))


def direct(n, odd, even):
    return min(mask.bit_count() + sum(not (mask >> u & 1 and mask >> v & 1) for u, v in even)
               for mask in range(1 << n) if all(mask >> u & 1 or mask >> v & 1 for u, v in odd))


def main():
    count = 0
    for n in range(1, 6):
        pairs = list(combinations(range(n), 2))
        for coloring in product(range(3), repeat=len(pairs)):
            odd = [e for e, state in zip(pairs, coloring) if state == 1]
            even = [e for e, state in zip(pairs, coloring) if state == 2]
            assert direct(n, odd, even) == quotient(n, odd, even), (n, odd, even)
            count += 1
    print(f"Direct cover search matched the component quotient on all {count:,} colored base graphs through five vertices.")


if __name__ == "__main__":
    main()
