#!/usr/bin/env python3
"""Check these independent Lean sources against a prepared official checkout."""
import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

FILES = {
    "CircuitCommitment.lean": (
        "OwnedRadix.Code.committed_output_iff",
        "OwnedRadix.Code.efficient_opening",
        "OwnedRadix.Code.commitment_function",
        "OwnedRadix.Code.query_opening",
        "OwnedRadix.Compiler.realize_official",
    ),
    "StackTraffic.lean": (
        "BudgetGuard.time_guard",
        "DeterministicPadding.sigma_of_clock",
        "DeterministicPadding.sigma_of_sublinear_switches",
        "StackTrace.Atomic.switch_write_clock",
        "StackTrace.Atomic.switch_write_cost",
        "DeterministicPadding.sigma_of_transfer_budget",
    ),
    "ExplicitOpenings.lean": (
        "StackLayout.Wired.short_traverses",
        "StackLayout.Wired.short_machine_separation",
        "StackLayout.Wired.explicit_opening_barrier",
    ),
    "PascalReader.lean": (
        "StackLayout.Wired.finite_machine_separation",
        "PascalStream.labels_without_witness",
    ),
    "PhysicalRows.lean": ("StackTrace.PhysicalSigma.sigmaV_of_honest_bits",),
    "ExponentBudget.lean": ("TraceBudget.padded_size",),
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
EMPTY = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("project", type=Path, help="prepared pequalnp-proofs/lean directory")
    project = args.parse_args().project.resolve()
    bundle = Path(__file__).resolve().parent
    lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not (project / "lean-toolchain").is_file():
        sys.exit(f"Missing lean-toolchain in {project}")
    version = subprocess.run([lake, "env", "lean", "--version"], cwd=project,
                             capture_output=True, text=True, check=True)
    print(version.stdout.strip(), flush=True)
    for filename, expected in FILES.items():
        command = [lake, "env", "lean", "-j1", "-DElab.async=false", str(bundle / filename)]
        result = subprocess.run(command, cwd=project, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        seen = {name: {word.strip() for word in words.split(",") if word.strip()}
                for name, words in AXIOMS.findall(result.stdout)}
        seen.update((name, set()) for name in EMPTY.findall(result.stdout))
        missing = set(expected) - seen.keys()
        extra = set().union(*(seen.get(name, set()) for name in expected)) - ALLOWED
        if result.returncode or missing or extra:
            print(result.stdout, file=sys.stderr)
            sys.exit(f"{filename} failed: exit={result.returncode}, "
                     f"missing={sorted(missing)}, extra axioms={sorted(extra)}")
        print(f"{filename} passed", flush=True)
        for name in expected:
            print(f"  {name}: {', '.join(sorted(seen[name])) or 'none'}", flush=True)


if __name__ == "__main__":
    main()
