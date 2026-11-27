"""Replay the 141-row certificate from the canonical Lean data and the readable sign list."""
from pathlib import Path
import json
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "certificate-k3"))
from leandata import matrix_text, row, table


def main():
    module = "Data3Split"
    with tempfile.TemporaryDirectory(prefix="grothendieck-141-") as name:
        work = Path(name)
        second = work / "second"
        second.mkdir()
        (second / "matrix.txt").write_text(matrix_text(table(module, "mSplitRows")), encoding="ascii")
        witness = json.loads((HERE / "second/witness-parameters.json").read_text())
        witness["alice_numerators"] = table(module, "aSplitRows")
        witness["bob_numerators"] = table(module, "bSplitRows")
        witness["classical_alice_signs"] = row(module, "sSplitRow")
        (second / "witness.json").write_text(json.dumps(witness, sort_keys=True) + "\n")
        with (HERE / "second/near-signings.txt").open() as rows, (second / "band.bin").open("wb") as out:
            for line in rows:
                out.write(struct.pack("<6I", *map(int, line.split())))
        manifest = HERE / "SHA256SUMS.json"
        for rel in json.loads(manifest.read_text()):
            if rel in {"second/matrix.txt", "second/witness.json", "second/band.bin"}:
                continue
            target = work / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(HERE / rel, target)
        shutil.copyfile(manifest, work / manifest.name)
        subprocess.run([sys.executable, "-B", str(work / "verify_strongest.py"), *sys.argv[1:]], check=True)


if __name__ == "__main__":
    main()
