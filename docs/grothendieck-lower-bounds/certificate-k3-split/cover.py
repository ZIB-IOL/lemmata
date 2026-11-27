"""Compute a rigorous signed-gain cap for each protected prefix from an orbit cover."""

import json
import subprocess
from pathlib import Path


def matrix(path):
    return [
        list(map(int, line.split()))
        for line in Path(path).read_text().splitlines()
        if line.strip()
    ]


def caps(base, lifted, indices, symmetry, cover, solver, work, threads):
    n, m = len(base), len(base[0])
    assert len(lifted) == n + len(indices)
    alt = [[0] * m for _ in base]
    for h, i in enumerate(indices):
        alt[i] = [a - b for a, b in zip(lifted[i], base[i])]
        assert [a - b for a, b in zip(base[i], alt[i])] == lifted[n + h]
    gcount = symmetry[0][2]
    p, reps = symmetry[0][0], symmetry[1]
    assert len(symmetry) == 2 + 4 * gcount and len(reps) == symmetry[0][1]
    mul, den = cover["multiplier"], cover["denominator"]
    assert type(mul) is int and mul > 1 and type(den) is int and den > 0
    ids, numerator = cover["indices"], cover["weight_numerators"]
    assert len(ids) == len(numerator) == len(set(ids))
    assert all(type(i) is int and 0 <= i < n for i in ids)
    assert all(type(w) is int and w >= 0 for w in numerator)
    mass = [0] * n
    for g in range(gcount):
        rowmap = symmetry[2 + 4 * g]
        for i, w in zip(ids, numerator):
            mass[rowmap[i]] += w
    assert mass == [den * gcount] * n
    # Work on rounded block rows. All their rounding errors are added back.
    scale = 4
    div = den * scale
    error = 0
    fixed, other = [], []
    for i, w in zip(ids, numerator):
        if w == 0:
            continue
        opts = [[w * x for x in base[i]], [w * mul * x for x in alt[i]]]
        rr = [[(x + div // 2) // div for x in row] for row in opts]
        error += max(
            sum(abs(x - div * y) for x, y in zip(row, rd)) for row, rd in zip(opts, rr)
        )
        item = (i, rr[0] + rr[1], max(sum(map(abs, side)) for side in rr))
        (fixed if i < p else other).append(item)
    assert fixed and all(i not in indices for i, _, _ in fixed)
    other.sort(key=lambda item: -item[2])
    input_file = work / "cover_block.txt"
    input_file.write_text(
        "".join(" ".join(map(str, row)) + "\n" for _, row, _ in fixed + other)
    )
    values = list(
        map(
            int,
            subprocess.check_output(
                [str(solver), str(input_file), str(len(fixed)), str(threads)], text=True
            ).split(),
        )
    )
    assert len(values) == 1 << (len(fixed) - 1)
    # For each image, the signs on the fixed sample rows come from the actual
    # retained base prefix. Global sign inversion fixes its first sign to +.
    entries = []
    for g in range(gcount):
        pa, sa = symmetry[2 + 4 * g : 4 + 4 * g]
        assert all(0 <= pa[i] < p for i, _, _ in fixed)
        entries.append([(pa[i], sa[i]) for i, _, _ in fixed])
    answer = {}
    for rep in reps:
        a = [1] + [1 - 2 * ((rep >> (i - 1)) & 1) for i in range(1, p)]
        total = 0
        for row in entries:
            first = a[row[0][0]] * row[0][1]
            mask = sum(
                1 << (k - 1) for k, (i, s) in enumerate(row) if k and a[i] * s * first < 0
            )
            total += values[mask]
        answer[rep] = (total * div + gcount * error + gcount * den - 1) // (gcount * den)
    return answer
