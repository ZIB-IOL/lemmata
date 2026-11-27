"""Compare near-list generation, surrogate screening and column transfer with brute force."""

import itertools, struct, subprocess, random
from fractions import Fraction as F
from test_certificate import put
from cover import caps


def run(tmp, band_solver, rounded_solver, block_solver):
    rng = random.Random(71103)
    for game in range(6):
        n = 6
        m = 7
        k = 4
        I = list(range(2, 6))
        R = [[rng.randrange(-12, 13) for _ in range(m)] for _ in range(n)]
        D = [[rng.randrange(-7, 8) for _ in range(m)] for _ in I]
        K = [[2 * x for x in row] for row in R]
        for h, i in enumerate(I):
            K[i] = [x + y for x, y in zip(R[i], D[h])]
            K.append([x - y for x, y in zip(R[i], D[h])])
        UY = [[x + rng.randrange(-3, 4) for x in row] for row in K]
        all_a = [(1,) + v for v in itertools.product((1, -1), repeat=n + k - 1)]
        dot = lambda x, y: sum(t * u for t, u in zip(x, y))

        def score(M, a):
            return sum(abs(dot(a, col)) for col in zip(*M))

        sy = [[2, 2, 1], [0, 1], list(range(n)), [1] * n, list(range(m)), [1] * m]
        for filename, rows in [("r", R), ("k", K), ("i", [I]), ("s", sy), ("su", UY)]:
            put(tmp / filename, rows)
        orig = [((1,) + v) for v in itertools.product((1, -1), repeat=n - 1)]
        CC = max(score(R, a) for a in orig)
        margin = 7
        target = CC - margin
        cv = {
            "multiplier": 4,
            "denominator": 1,
            "indices": list(range(n)),
            "weight_numerators": [1] * n,
        }
        U = caps(R, K, I, sy, cv, block_solver, tmp, 1)
        raw = max(
            sum(abs(dot(b, row)) for row in D) for b in itertools.product((1, -1), repeat=m)
        )
        L = {p: min(raw, max(0, (v - target + 2) // 3)) for p, v in U.items()}
        largest = max(L.values())
        cut = target - largest
        assert cut >= 0

        def pack(threshold):
            data = [
                (score(R, a), sum(1 << i for i, x in enumerate(a) if x < 0), 0, 0)
                for a in orig
                if score(R, a) > threshold
            ]
            (tmp / "near").write_bytes(
                b"K3SIG001"
                + struct.pack("<IIIQ", n, m, threshold, len(data))
                + b"".join(struct.pack("<4I", *t) for t in data)
            )

        pack(cut)
        put(tmp / "caps", L.items())
        subprocess.run(
            [
                str(band_solver),
                *[str(tmp / f) for f in ("r", "k", "i", "s", "near")],
                str(cut),
                str(CC),
                "1",
                str(largest),
                str(tmp / "caps"),
                str(tmp / "list"),
                str(margin),
            ],
            stdout=subprocess.DEVNULL,
            check=True,
        )

        def unpack(file):
            return {
                (r[0], tuple(1 - 2 * ((r[1 + i // 32] >> (i % 32)) & 1) for i in range(n + k)))
                for r in struct.iter_unpack("<6I", file.read_bytes())
            }

        expected = {(score(K, a) // 2, a) for a in all_a if score(K, a) > 2 * target}
        actual = unpack(tmp / "list")
        assert actual == expected
        sh = CC - 32
        gate = 2 * CC - 64
        pack(sh)
        subprocess.run(
            [
                str(rounded_solver),
                str(tmp / "r"),
                str(tmp / "i"),
                str(tmp / "near"),
                str(sh),
                "1",
                str(tmp / "shallow"),
                str(tmp / "su"),
                str(gate),
            ],
            stdout=subprocess.DEVNULL,
            check=True,
        )
        true = set()
        for a in all_a:
            x = list(a[:n])
            for h, i in enumerate(I):
                x[i] = (a[i] + a[n + h]) // 2
            norm = score(R, x)
            if norm > sh and score(UY, a) > gate:
                true.add((norm, a))
        assert unpack(tmp / "shallow") == true
        # A nonsymmetric perturbation on all rows and an added split column.
        M = [[2 * x for x in row] for row in R]
        s = F(3, 4)
        for h, i in enumerate(I):
            M[i] = [x + s * y for x, y in zip(R[i], D[h])]
            M.append([x - s * y for x, y in zip(R[i], D[h])])
        hcol = [rng.randrange(-2, 3) for _ in K]
        eps = [[rng.randrange(-1, 2) for _ in range(m)] for _ in K]
        pert = [[x + y for x, y in zip(row, extra)] for row, extra in zip(M, eps)]
        U0 = max(score(eps, a) for a in all_a) + sum(map(abs, hcol))

        def multi(a):
            columns = [dot(a, c) for c in zip(*pert)]
            return sum(map(abs, columns)) + max(0, abs(dot(a, hcol)) - abs(columns[0]))

        best = max(multi(a) for a in all_a)
        assert best <= max([2 * target + U0 / s] + [multi(a) for _, a in actual])
    print(
        "Six brute-force near-list, surrogate and joint row/column perturbation tests passed.",
        flush=True,
    )
