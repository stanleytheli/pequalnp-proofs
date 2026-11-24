"""Write the bounded-occurrence CNF reduction in standard DIMACS format."""
import argparse
import json
from pathlib import Path

from succinct_gap import planted


def read_dimacs(path):
    header = None
    clause = []
    clauses = []
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields or fields[0] == "c":
            continue
        if fields[0] == "p":
            if header or len(fields) != 4 or fields[1] != "cnf":
                raise ValueError("expected one DIMACS p cnf header")
            header = (int(fields[2]), int(fields[3]))
            continue
        for token in fields:
            value = int(token)
            if value:
                clause.append(value)
            else:
                clauses.append(tuple(clause))
                clause = []
    if clause or header is None or len(clauses) != header[1] or min(header) < 0:
        raise ValueError("DIMACS header/clauses disagree")
    return header[0], clauses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--order", type=int, required=True, help="order of the HC to plant")
    parser.add_argument("--witness", help="satisfying SAT assignment as a string of 0/1 bits")
    parser.add_argument("--projection", type=Path, help="write the witness-induced literal map as JSON")
    args = parser.parse_args()
    bits, clauses = read_dimacs(args.source)
    if (args.witness is None) != (args.projection is None):
        parser.error("supply --witness and --projection together")
    try:
        _, enc, rails, edges, _ = planted(clauses, bits, args.order)
    except ValueError as exc:
        parser.error(str(exc))
    if args.projection is not None:
        if len(args.witness) != bits or set(args.witness)-{"0", "1"}:
            parser.error("witness must have one 0/1 position per source bit")
        chosen = [int(s) for s in args.witness]
        if not all(any(chosen[abs(l)-1] == (l > 0) for l in row) for row in clauses):
            parser.error("the supplied assignment does not satisfy the source formula")
        weights = {enc.representative[1]: 0}
        for pair, value in zip(rails, chosen):
            weights[enc.representative[pair[1-value]]] = 0
        for i, row in enumerate(edges):
            for j, v in enumerate(row):
                weights[enc.representative[v]] = f"X[{i},{j}]"
        data = {"target_order": args.order, "default_image": 1, "images": weights}
        args.projection.write_text(json.dumps(data, indent=2, sort_keys=True)+"\n")
    print(f"c known one-hot satisfying exponent is variable {enc.representative[1]}")
    print(f"p cnf {len(enc.signed_copies)-1} {len(enc.clauses)}")
    for clause in enc.clauses:
        print(*clause, 0)


if __name__ == "__main__":
    main()
