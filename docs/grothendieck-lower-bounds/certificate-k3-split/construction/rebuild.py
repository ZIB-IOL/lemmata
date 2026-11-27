"""Reconstruct every matrix row from the base, seed displacements, and signed maps."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def rows(p):
    return [list(map(int, l.split())) for l in p.read_text().splitlines()]


def rebuild():
    base = rows(ROOT / "base.txt")
    sym = rows(ROOT / "symmetry.txt")
    gen = json.loads((ROOT / "construction/generator.json").read_text())
    rebuilt = [[2 * x for x in r] for r in base]
    used = []
    for orbit in gen["orbits"]:
        i, d = orbit["seed_row"], orbit["displacement"]
        assert len(d) == len(base[0])
        for g in orbit["maps"]:
            pa, sa, pb, sb = sym[2 + 4 * g : 6 + 4 * g]
            index = pa[i]
            v = [0] * len(d)
            for j, x in enumerate(d):
                v[pb[j]] = sa[i] * sb[j] * x
            rebuilt[index] = [a + b for a, b in zip(base[index], v)]
            rebuilt.append([a - b for a, b in zip(base[index], v)])
            used.append(index)
    assert len(used) == len(set(used)) and used == list(
        map(int, (ROOT / "split_rows.txt").read_text().split())
    )
    assert rebuilt == rows(ROOT / "lifted_matrix.txt")
    return rebuilt


if __name__ == "__main__":
    print("Verified complete matrix reconstruction.", len(rebuild()), "rows.")
