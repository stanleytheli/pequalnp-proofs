"""Complete the small integer checks used in the Heawood formula-cone argument."""
from itertools import product
from pathlib import Path
import subprocess
from cone_profiles import EDGES, bitset, orbit, transformations

BASE = Path(__file__).resolve().parent
EXPECTED = {
    (63, 16383, 3): 60,
    (63, 16383, 4): 65,
    (969, 16383, 3): 61,
    (969, 16383, 4): 65,
    (975, 16139, 3): 52,
    (1599, 1534, 3): 60,
}


def check():
    for args, expected in EXPECTED.items():
        output = subprocess.check_output([str(BASE / 'rectpack'), *map(str, args)], text=True)
        p, q, r, val, _ = map(int, output.split())
        assert (p, q, r) == args and val == expected
        print(p, q, r, val)
    perms = transformations()
    assert len(perms) == 336
    profiles = {p for p, q in orbit((969, 16383), perms)}
    assert len(profiles) == 28
    vertices = lambda rows: {v for i in bitset(rows) for v in EDGES[i]}
    full = (1 << len(EDGES)) - 1
    assert min(len(vertices(full & ~(p | q))) for p, q in product(profiles, repeat=2)) == 10
    for p in profiles:
        assert len(vertices(p)) == 8 and len(list(bitset(p))) == 6
    print("Two exceptional cones leave at least ten raw vertices.")


if __name__ == '__main__':
    check()
