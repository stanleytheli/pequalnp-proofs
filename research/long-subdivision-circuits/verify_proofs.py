"""Rebuild the subdivision modules against an existing, built project checkout."""
import argparse
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


MODULES = [
    "SubdivisionLayout", "StarForest", "PathCoverCost", "MixedOutcomes", "GirthGrowth",
    "SevenLayout", "SubdivisionPath", "SubdivisionUpper", "SubdivisionTheorems",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="built project's lean directory")
    parser.add_argument("--lean", type=Path, required=True, help="pinned Lean binary")
    args = parser.parse_args()
    src = Path(__file__).resolve().parent
    project = args.project.resolve()
    lean = args.lean.resolve(strict=True)
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    if "version 4.36.0" not in version:
        raise SystemExit("Expected Lean 4.36.0. Found " + version)
    project_lib = project / ".lake/build/lib/lean"
    imported = project_lib / "PEqualNP/Outside/L_meta_575.olean"
    if not imported.is_file():
        raise SystemExit("Build PEqualNP.Outside.L_meta_575 in the project first.")
    dependencies = sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean"))
    with TemporaryDirectory() as tmp:
        env = dict(os.environ)
        env["LEAN_PATH"] = os.pathsep.join(map(str, [tmp, project_lib, *dependencies]))
        audits = 0
        for module in MODULES:
            target = Path(tmp) / (module + ".olean")
            proc = subprocess.run([lean, "--root=" + str(src), "-j1", "-DElab.async=false",
                                   "-o", target, src / (module + ".lean")],
                                  env=env, capture_output=True, text=True)
            output = proc.stdout + proc.stderr
            print(output, end="", flush=True)
            if proc.returncode or not target.is_file() or "sorryAx" in output:
                raise SystemExit("Kernel check failed in " + module)
            for names in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
                if set(names.split(", ")) - ALLOWED:
                    raise SystemExit("Unexpected axiom in " + module)
                audits += 1
    if not audits:
        raise SystemExit("No named axiom audits were observed.")
    print(f"Rebuilt {len(MODULES)} modules; checked {audits} named axiom lists.")


if __name__ == "__main__":
    main()
