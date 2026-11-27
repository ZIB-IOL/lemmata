"""Check a fixed-vector upper bound for any invariant change to the second reference matrix."""

from fractions import Fraction as F
import math, json
from refinement import dot


def ceil_root(x):
    return math.isqrt(x) + (math.isqrt(x) ** 2 != x)


def bound(w, center, perms, certificate, all_chsh=True):
    Q = w["vector_denominator"]
    X = w["alice_numerators"]
    Y = w["bob_numerators"]
    n = len(X)
    m = len(Y)
    assert len(center) == n and len(center[0]) == m
    wd = certificate["weight_denominator"]
    fd = certificate["factor_denominator"]
    assert type(wd) is int and type(fd) is int and min(wd, fd) > 0
    weights = certificate["weights"]
    A = certificate["alice"]
    B = certificate["bob"]
    fact = certificate["factor"]
    r = fact[:n]
    c = fact[n:]
    assert len(r) == n and len(c) == m and len({len(row) for row in fact}) == 1
    assert all(type(v) is int for row in fact for v in row)
    assert len(A) == len(B) == len(weights) and all(type(x) is int and x >= 0 for x in weights)
    assert all(len(u) == n and all(t in (-1, 1) for t in u) for u in A) and all(
        len(u) == m and all(t in (-1, 1) for t in u) for u in B
    )
    common = math.lcm(Q**2, wd, fd**2)
    gscale = common // Q**2
    sscale = common // wd
    fscale = common // fd**2
    # Pack all weighted Bob signs to form the full classical sum exactly in parallel columns.
    half = 1 << 63
    assert sum(weights) < half

    def pack(row):
        result = 0
        for v in reversed(row):
            result = (result << 64) + v
        return result

    import struct

    blocks = [h * pack(row) for h, row in zip(weights, B)]
    off = pack([half] * m)
    unpack = struct.Struct("<" + "Q" * m).unpack
    residual = []
    on_center = 0
    original = []
    for i, row in enumerate(center):
        signed = off + sum(a[i] * t for a, t in zip(A, blocks))
        sum_signs = unpack(signed.to_bytes(8 * m, "little"))
        vals = [gscale * dot(X[i], y) - sscale * (t - half) for y, t in zip(Y, sum_signs)]
        original.append(vals)
        on_center += dot(vals, row)
        residual.append([v - fscale * dot(r[i], z) for v, z in zip(vals, c)])
    # Each invariant matrix is constant, up to these recorded signs, on every
    # coordinate orbit. A sign conflict forces the coefficient to vanish.
    seen = set()
    largest = F(0)
    projected = [[0] * m for _ in range(n)]
    ng = len(perms)
    for i in range(n):
        for j in range(m):
            if (i, j) in seen:
                continue
            entries = {}
            conflict = False
            for pa, sa, pb, sb in perms:
                key = (pa[i], pb[j])
                sg = sa[i] * sb[j]
                if key in entries and entries[key] != sg:
                    conflict = True
                entries[key] = sg
            assert (i, j) in entries and not (set(entries) & seen)
            seen.update(entries)
            if not conflict:
                err = sum(s * residual[a][b] for (a, b), s in entries.items())
                largest = max(largest, F(abs(err), len(entries) * common))
                zz, rem = divmod(
                    ng * sum(s * original[a][b] for (a, b), s in entries.items()), len(entries)
                )
                assert rem == 0
                for (a, b), s in entries.items():
                    projected[a][b] = s * zz
    assert len(seen) == n * m
    corr = F(ceil_root(max(dot(x, x) for x in r) * max(dot(x, x) for x in c)), fd**2)
    # The columns of the remaining matrix have norm at most sqrt(n) times
    # the largest entry. Unit coordinate vectors give an explicit factorization.
    z = max(
        F(0),
        F(on_center, common * 2 * (320975646 - w["reference_margin"])),
        corr + ceil_root(n) * largest,
    )
    if certificate.get("comparison") == "column contractions":
        # The support function of the maximum absolute row-sum ball has this explicit form.
        projcols = list(zip(*projected))
        basecols = list(zip(*center))
        support = 0
        for col in basecols:
            support += max(abs(dot(col, y)) for y in projcols)
        z = max(z, F(support, ng * common * 2 * (320975646 - w["reference_margin"])))
    if "small_game_budget" in w and all_chsh:
        # Price every signed 2-by-2 CHSH embedding, before or after symmetry averaging.
        high = 0
        for i, r1 in enumerate(projected):
            for r2 in projected[i:]:
                plus = max(abs(a + b) for a, b in zip(r1, r2))
                minus = max(abs(a - b) for a, b in zip(r1, r2))
                high = max(high, plus + minus)
        z = max(z, F(high, 2 * ng * common))
    if "small_game_budget" in w and not all_chsh:
        for i, k, j, l, s, t in certificate["chsh_dictionary"]:
            assert (
                all(type(h) is int for h in (i, k, j, l))
                and 0 <= i < n
                and 0 <= k < n
                and 0 <= j < m
                and 0 <= l < m
                and s in (-1, 1)
                and t in (-1, 1)
            )
            val = s * (projected[i][j] + projected[k][j]) + t * (
                projected[i][l] - projected[k][l]
            )
            z = max(z, F(val, 2 * ng * common))
    if "dictionary_arrays" in certificate:
        from dictionary import item
        from cover import matrix
        from pathlib import Path

        original_base = matrix(Path(__file__).resolve().parent / "base.txt")
        for elem in certificate["dictionary_arrays"]:
            atom, cap = item(original_base, perms, elem, n, m, center, w["reference_classical"])
            value = sum(dot(row, col) for row, col in zip(atom, projected))
            z = max(z, F(value, cap * ng * common))
    upper = F(sum(weights), wd) + z
    prefix = "upper" if all_chsh else "listed_upper"
    if prefix + "_numerator" in certificate:
        assert upper == F(
            certificate[prefix + "_numerator"], certificate[prefix + "_denominator"]
        )
    return upper, largest
