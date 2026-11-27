"""Match the Lean inputs to the supplement and replay the classical certificate."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "certificate-k3"))
from leandata import matrix_text, row, table

ARCHIVE_SHA256 = "cbdb454d30c508dd7cc4c26b565a280bb2ce705a86cd21e3302b838e3b7cb4ef"


def main():
    if not __debug__:
        raise RuntimeError("Run the verifier with assertions enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--from-scratch", action="store_true",
                        help="also regenerate the parent Alice sign list from the 81-row base")
    args = parser.parse_args()
    archive = HERE / "computation.zip"
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    if digest != ARCHIVE_SHA256:
        raise ValueError(f"Unexpected SHA-256 for {archive.name}: {digest}")
    with tempfile.TemporaryDirectory(prefix="grothendieck-301-") as tmp:
        work = Path(tmp)
        with zipfile.ZipFile(archive) as files:
            lean_matrix = matrix_text(table("Data3Orbit", "mOrbitRows")).encode("ascii")
            assert lean_matrix == files.read("witness/matrix.txt")
            vectors = json.loads(files.read("witness/final-vectors.json"))
            assert vectors["denominator"] == 10**40
            assert table("Data3Orbit", "aOrbitRows") == vectors["alice"]
            assert table("Data3Orbit", "bOrbitRows") == vectors["bob"]
            mask = json.loads(files.read("witness/calibration.json"))["mask"]
            signs = [1 - 2 * ((mask[j // 64] >> (j % 64)) & 1) for j in range(321)]
            assert row("Data3Orbit", "sOrbitRow") == signs
            files.extractall(work)
        print("Lean matrix, 622 vector triples and attaining Bob signing match the supplement.", flush=True)
        command = [sys.executable, "-B", "certificate.py", "--threads", str(args.threads)]
        if args.from_scratch:
            command.append("--from-scratch")
        subprocess.run(command, cwd=work, check=True)


if __name__ == "__main__":
    main()
