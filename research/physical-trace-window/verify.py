#!/usr/bin/env python3
"""Check each local Lean module, its named theorems and their transitive axioms."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

THEOREMS = {'FP3KernelC': ['OwnedRadix.Compiler.realize_official', 'OwnedRadix.Code.commitment_function'],
 'FP3KernelR': ['StackTrace.PhysicalSigma.sigmaV_of_honest_bits',
                'StackTrace.streaming_reference',
                'StackTrace.sweep_rows',
                'StackTrace.physicalSweep_bit',
                'StackTrace.physicalSweep_shape'],
 'FP3Bases': [],
 'FP3GameBase': ['StackTrace.CircuitRows.framed_circuit',
                 'StackTrace.CircuitRows.opened_bit',
                 'StackTrace.CircuitRows.sigmaV_of_circuit_rows',
                 'StackTrace.RowAddress.widths',
                 'StackTrace.RowAddress.sigmaV_of_short_row_tables',
                 'StackTrace.RowAccess.count',
                 'StackTrace.RowAccess.check_congr',
                 'StackTrace.RowAccess.canonical_in_range',
                 'StackTrace.RowAccess.finite_view',
                 'StackTrace.RowAccess.arbitrary_footprint_lt',
                 'StackTrace.RowAccess.single_bit_refutations',
                 'StackTrace.RowAccess.Codec.represent',
                 'StackTrace.RowAccess.universal_sound',
                 'StackTrace.RowAccess.universal_complete'],
 'FP3Game': ['StackTrace.RowAccess.refuted_iff_response',
             'StackTrace.OneOpeningGame.sigmaV_of_single_opening',
             'StackTrace.OneOpeningGame.word_game'],
 'FP3Columns': ['ColumnCheck.Formula.correct', 'ColumnCheck.serial_rows', 'ColumnCheck.physical'],
 'FP3Window': ['ColumnCheck.Tree.test_correct',
               'ColumnCheck.allValues_get',
               'ColumnCheck.Pointer.all_stacks',
               'ColumnCheck.Control.command_value',
               'ColumnCheck.Control.peek_value',
               'ColumnCheck.Control.stateTest_eval',
               'ColumnCheck.Runtime.checks',
               'ColumnCheck.Runtime.all_checks',
               'ColumnCheck.Table.check_iff',
               'ColumnCheck.Table.decoded_table',
               'ColumnCheck.Table.counter_iff',
               'ColumnCheck.Table.physical_counter'],
 'FP3WireCodec': ['ColumnCheck.Wire.row_recover',
                  'ColumnCheck.Wire.represent',
                  'ColumnCheck.Wire.represent_word'],
 'FP3SourceRead': ['DyadicLookup.physical_lookup', 'DyadicLookup.physical_binary_address']}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PATTERN = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
EMPTY = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="pinned, prebuilt public project's lean directory")
    project = parser.parse_args().project.resolve()
    source = Path(__file__).resolve().parent
    lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not (project / "lean-toolchain").is_file():
        raise SystemExit(f"No lean-toolchain in {project}")
    def from_lake(*args):
        return subprocess.run([lake, "env", *args], cwd=project, capture_output=True,
                              text=True, check=True).stdout.strip()
    lean = from_lake("which", "lean")
    print(from_lake("lean", "--version"), flush=True)
    with tempfile.TemporaryDirectory(prefix="fp3-lean-") as build:
        environment = {**os.environ, "LEAN_PATH": build + os.pathsep + from_lake("printenv", "LEAN_PATH")}
        for module, required in THEOREMS.items():
            command = [lean, "-j1", "-DElab.async=false", f"--root={source}",
                       "-o", str(Path(build) / f"{module}.olean"), str(source / f"{module}.lean")]
            result = subprocess.run(command, cwd=project, env=environment, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            found = {name: {x.strip() for x in axs.split(",") if x.strip()}
                     for name, axs in PATTERN.findall(result.stdout)}
            found.update((name, set()) for name in EMPTY.findall(result.stdout))
            unapproved = {name: sorted(axs - ALLOWED) for name, axs in found.items() if axs - ALLOWED}
            missing = set(required) - set(found)
            if result.returncode or missing or unapproved:
                print(result.stdout)
                raise SystemExit(f"{module} failed, exit {result.returncode}, missing {sorted(missing)}, axioms {unapproved}")
            print(f"{module} passed", flush=True)
            for name in required:
                print(f"  {name}    {', '.join(sorted(found[name])) or 'none'}", flush=True)


if __name__ == "__main__":
    main()
