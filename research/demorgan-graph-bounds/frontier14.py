"""Summarize or independently replay the saved fourteen-input circuit bounds."""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true", help="rerun the C++ search for every recorded row")
    parser.add_argument("--remaining", type=Path, help="write the unresolved encoding and upper bound pairs")
    args = parser.parse_args()
    targets = dict(tuple(map(int, line.split())) for line in (ROOT/"catalogue-14.txt").read_text().splitlines())
    assert len(targets) == 2765
    solved = set()
    with TemporaryDirectory() as tmp:
        binary = Path(tmp)/"lower14"
        if args.replay:
            subprocess.run(["c++", "-std=c++17", "-O3", "-DVERTICES=14", ROOT/"larger.cpp", "-o", binary], check=True)
        for depth in (5, 8, 10, 12):
            rows = [tuple(map(int, x.split())) for x in (ROOT/f"fourteen{depth}.txt").read_text().splitlines()]
            unique = {mask for mask, _, _, _ in rows}
            assert len(rows) == len(unique) and unique <= targets.keys() - solved
            if depth < 12:
                assert unique == targets.keys() - solved
            for mask, lower, upper, _ in rows:
                assert 0 <= lower <= upper == targets[mask]
                if lower == upper:
                    solved.add(mask)
            if args.replay:
                todo = Path(tmp)/"graphs.txt"
                todo.write_text("".join(f"{mask} {upper}\n" for mask, _, upper, _ in rows))
                result = subprocess.run([binary, str(depth), "13", todo], check=True, text=True, capture_output=True)
                observed = {}
                for line in result.stdout.splitlines():
                    mask, lower, upper, _ = map(int, line.split())
                    observed[mask] = (lower, upper)
                assert observed.keys() == unique
                assert all(lower <= observed[mask][0] <= upper == observed[mask][1] for mask, lower, upper, _ in rows)
    print(f"{len(solved)} of {len(targets)} fourteen-input classes reached their explicit upper bound.")
    if args.remaining:
        args.remaining.write_text("".join(f"{mask} {upper}\n" for mask, upper in targets.items() if mask not in solved))


if __name__ == "__main__":
    main()
