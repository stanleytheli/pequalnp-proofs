"""Verify the release and replay the main finite controls with standard Python."""
from hashlib import sha256
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
expected = {}
for line in (root / "SHA256SUMS").read_text().splitlines():
    digest, path = line.split("  ", 1)
    expected[path] = digest
for path, digest in expected.items():
    if sha256((root / path).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Checksum failed for {path}")
print(f"Verified {len(expected)} file checksums", flush=True)
checks = ["check_local.py", "check_junta.py", "check_tradeoff.py", "check_boolean_gap.py", "check_signal_layout.py",
          "check_certificate_search.py", "check_balanced.py", "check_graph_verifier.py"]
for script in checks:
    subprocess.run([sys.executable, "-B", script], cwd=root / "investigations", check=True)
