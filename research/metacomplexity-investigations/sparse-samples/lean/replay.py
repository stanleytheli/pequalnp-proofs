"""Elaborate the five original modules against an existing Lean 4.36.0 Mathlib checkout."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mathlib", type=Path, help="Existing compiled Mathlib checkout")
    parser.add_argument("--lean", default="lean", help="Lean 4.36.0 executable")
    args = parser.parse_args()
    mathlib = args.mathlib.resolve()
    source = Path(__file__).resolve().parent
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if "version 4.36.0," not in version:
        raise SystemExit("Expected Lean 4.36.0; detected " + version)
    print(version, flush=True)
    deps = [mathlib / ".lake/build/lib/lean", *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    if not (deps[0] / "Mathlib").is_dir():
        raise SystemExit("Expected a compiled Mathlib object tree at " + str(deps[0]))
    with tempfile.TemporaryDirectory() as build:
        env = {**os.environ, "LEAN_PATH": os.pathsep.join([build, *map(str, deps)])}
        for module in ("FormulaRank", "PointwiseFormula", "ReadOptimal", "ReadBudgets", "CappedMinimum"):
            run = subprocess.run([args.lean, "-j1", "-DElab.async=false", "--root=" + str(source),
                                  "-o", str(Path(build) / (module + ".olean")), str(source / (module + ".lean"))],
                                 cwd=mathlib, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            print(run.stdout, end="", flush=True)
            run.check_returncode()
            if "depends on axioms:" not in run.stdout or "sorryAx" in run.stdout:
                raise SystemExit("Failed axiom-inventory check for " + module)
            print("PASS", module, flush=True)


if __name__ == "__main__":
    main()
