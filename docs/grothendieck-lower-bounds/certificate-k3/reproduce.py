"""Rebuild and run the complete integer certificate, then check the vectors.

Requirements: Python >=3.9; a C++17 compiler supporting OpenMP (default: g++).
No Python packages, floating-point solver, or network connection are needed.
Run from a clone of the repository: the matrix and the vectors are read from
lean/Lemmata/GrothendieckLowerBounds/Data3.lean, where they are stored once.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tempfile
import time

import sys
sys.dont_write_bytecode = True
import leandata  # noqa: E402

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--compiler", default="g++")
    parser.add_argument("--enumerate-near", action="store_true",
                        help="also exhaustively collect strategies above 319975296")
    args = parser.parse_args()
    assert 1 <= args.threads <= 256
    manifest = json.loads((ROOT / "SHA256SUMS.json").read_text())
    for name, expected in manifest.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, name
    print("All packaged source and input hashes match.", flush=True)
    # The matrix in the search order, generated from the Lean data and checked against the
    # hashes of the inputs of the recorded run (provenance.json).
    recorded = json.loads((ROOT / "provenance.json").read_text())
    recorded = recorded["fresh_classical_verification"]["input_file_sha256_at_start"]
    matrix = leandata.table("Data3", "m3Rows")
    order = [int(x) for x in (ROOT / "row_order.txt").read_text().split()]
    assert sorted(order) == list(range(len(matrix)))
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="grothendieck-three-") as temp:
        inputs = {"matrix.txt": leandata.matrix_text(matrix),
                  "ordered_matrix.txt": leandata.matrix_text([matrix[k] for k in order])}
        for name, text in inputs.items():
            data = text.encode()
            assert hashlib.sha256(data).hexdigest() == recorded[name], name
            (Path(temp) / name).write_bytes(data)
        print("The matrix in Data3.lean is the matrix of the recorded run.", flush=True)
        binary = Path(temp) / "verify_classical"
        subprocess.run([args.compiler, "-O3", "-std=c++17", "-fopenmp",
                        str(ROOT / "verify_classical.cpp"), "-o", str(binary)], check=True)
        command = [str(binary), str(Path(temp) / "matrix.txt"),
                   str(Path(temp) / "ordered_matrix.txt"), str(ROOT / "tail_bounds.txt"),
                   "320975296", str(args.threads), "21", "--symmetry",
                   str(ROOT / "symmetry.txt")]
        subprocess.run(command, check=True)
        if args.enumerate_near:
            command[4] = "319975296"
            output = Path.cwd() / "near_strategies.json"
            subprocess.run(command + ["--enumerate-above", "--counterexample-out",
                                       str(output)], check=True)
            data = json.loads(output.read_text())
            assert data["exhaustive_in_retained_symmetry_prefixes"]
            assert len(data["counterexamples"]) == 15497
            assert max(item["value"] for item in data["counterexamples"]) == 320975296
    from verify_quantum import verify
    verify()
    print("PASS: C(M) = 320975296 and K_G(3) > 1.43888070193021.")
    print(f"Elapsed seconds: {time.monotonic() - start:.3f}")


if __name__ == "__main__":
    main()
