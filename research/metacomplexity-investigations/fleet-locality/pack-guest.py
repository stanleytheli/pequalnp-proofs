"""Assemble the full physical wrapper against receipt-pinned fleet proof bodies."""
from hashlib import sha256
from pathlib import Path
from sys import argv
import json
project, receipt, wrapper, destination = map(Path, argv[1:])
spec = json.loads(receipt.read_text())
hashes = {entry["module"].rsplit(".", 1)[-1]: entry["sha256"].split(":")[1]
          for entry in spec["artifact"]["rests_on"]}
order = ["Shannon", "Support", "OrChain", "HittingSet", "Columns", "LocalFormat",
         "LocalConstruct", "LocalPrivate", "Elim", "Hardwire", "LocalMajority", "LocalMajorityQ"]
chunks = ["import PEqualNP.Defs\nimport Mathlib.Data.Fintype.Fin\nimport ParityEncoding\n"]
for name in order:
    source = project / "PEqualNP/MetaComplexity/Helpers" / (name + ".lean")
    assert sha256(source.read_bytes()).hexdigest() == hashes[name], name
    chunks.append("\n".join(line for line in source.read_text().splitlines() if not line.startswith("import ")))
chunks.append("\n".join(line for line in wrapper.read_text().splitlines() if not line.startswith("import ")))
destination.write_text("\n\n".join(chunks) + "\n")
