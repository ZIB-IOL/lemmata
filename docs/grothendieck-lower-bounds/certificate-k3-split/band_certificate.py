"""Reconstruct the second endpoint and verify a matrix within its certified neighborhood."""

import json, math, struct, subprocess
from fractions import Fraction as F
from pathlib import Path
from cover import matrix, caps
from refinement import dot


def read(p):
    return json.loads(p.read_text())


def second_endpoint(root, base, first, I, sym):
    d = root / "second"
    rec = read(d / "recipe.json")
    p = rec["previous_weights"]
    q = rec["denominator"]
    u = rec["multiplier_numerator"]
    v = rec["multiplier_denominator"]
    assert all(type(t) is int for t in p + [q, u, v]) and q > 0 and v > 0
    H = matrix(root / "extra_direction.txt")
    n = len(base)
    m = len(base[0])
    k = len(I)
    D = []

    def rounded(t, den):
        return (1 if t >= 0 else -1) * ((abs(t) + den // 2) // den)

    for h, i in enumerate(I):
        lam = p[4 + int(h >= k // 2)]
        D.append(
            [
                rounded(u * (lam * (x - y) + p[7] * z), v * q)
                for x, y, z in zip(first[i], base[i], H[h])
            ]
        )
    K = [[2 * z for z in row] for row in base]
    for h, i in enumerate(I):
        K[i] = [a + b for a, b in zip(base[i], D[h])]
        K.append([a - b for a, b in zip(base[i], D[h])])
    assert K == matrix(d / "endpoint.txt")
    loc = {i: h for h, i in enumerate(I)}
    perms = []
    for g in range(2, len(sym), 4):
        pa, sa, pb, sb = sym[g : g + 4]
        lift = pa + [pa[i] for i in I]
        sgn = sa + [sa[i] for i in I]
        for h, i in enumerate(I):
            nh = loc[pa[i]]
            a = all(D[nh][pb[j]] == sa[i] * sb[j] * v for j, v in enumerate(D[h]))
            lift[i], lift[n + h] = (pa[i], n + nh) if a else (n + nh, pa[i])
        assert sorted(lift) == list(range(n + k))
        assert all(
            K[lift[i]][pb[j]] == sgn[i] * sb[j] * v
            for i, row in enumerate(K)
            for j, v in enumerate(row)
        )
        perms.append((lift, sgn, pb, sb))
    return K, D, perms


def norm_square(delta, cert):
    # A residual around an integer Gram factor proves the upper by row sums.
    n = len(delta)
    a = cert["diagonal"]
    v = cert["reciprocals"]
    tr = cert["lower_triangular"]
    assert len(a) == len(tr) == n and all(len(row) == len(v) for row in delta)
    assert all(type(y) is int and y > 0 for y in a + v)
    assert all(
        len(row) == i + 1 and all(type(y) is int for y in row) for i, row in enumerate(tr)
    )
    weighted = [[t * w for t, w in zip(row, v)] for row in delta]
    error = 0
    for i in range(n):
        for j in range(i + 1):
            r = (a[i] if i == j else 0) - dot(weighted[i], delta[j]) - dot(tr[i], tr[j])
            error += (1 if i == j else 2) * abs(r)
    assert error == cert["error"]
    return (sum(a) + error) * sum(F(1, t) for t in v)


def norm(delta, cert):
    square = norm_square(delta, cert)
    u = math.isqrt(square.numerator // square.denominator) + 1
    assert u == cert["upper"]
    return u


def signed(w, root, base, first, I, sym, records, check_records=True):
    center, ds, perms = second_endpoint(root, base, first, I, sym)
    d = root / "second"
    k = len(I)
    n = len(base)
    m = len(base[0])
    q = w["scale_denominator"]
    t = w["base_numerator"]
    p = w["scale_numerators"]
    den = w["delta_denominator"]
    assert (
        type(q) is int
        and type(den) is int
        and q > 0
        and den > 0
        and q % den == 0
        and len(p) == 2
        and type(t) is int
        and t > 0
        and all(type(i) is int and 0 < i <= t for i in p)
    )
    delta = matrix(d / "delta.txt")
    assert len(delta) == n + k and all(len(row) == m for row in delta)
    U = norm(delta, read(d / "norm.json"))
    u = F(U, den)
    M = [[2 * t * x for x in row] for row in base]
    for h, i in enumerate(I):
        z = p[int(h >= k // 2)]
        M[i] = [t * x + z * y for x, y in zip(base[i], ds[h])]
        M.append([t * x - z * y for x, y in zip(base[i], ds[h])])
    M = [[x + (q // den) * z for x, z in zip(row, h)] for row, h in zip(M, delta)]
    if w.get("comparison") == "column contractions":
        W = matrix(d / "transport.txt")
        assert len(W) == m and all(len(row) == m for row in W)
        mass = max(sum(map(abs, row)) for row in W)
        assert mass == w["transport_mass"]
        for ra, rs, cb, cs in perms:
            assert all(
                W[cb[i]][cb[j]] == cs[i] * cs[j] * v
                for i, row in enumerate(W)
                for j, v in enumerate(row)
            )
            assert all(
                delta[ra[i]][cb[j]] == rs[i] * cs[j] * v
                for i, row in enumerate(delta)
                for j, v in enumerate(row)
            )
        stream = [[(j, v) for j, v in enumerate(row) if v] for row in W]
        M = []
        for row, er in zip(center, delta):
            y = [(q // den) * v for v in er]
            for x, items in zip(row, stream):
                for j, c in items:
                    y[j] += x * c
            M.append(y)
    game_budget = 0
    if "small_game_budget" in w:
        from games import changes

        extra, game_budget = changes(perms, read(d / "games.json"), len(M), m)
        assert game_budget == w["small_game_budget"]
        M = [[x + y for x, y in zip(row, part)] for row, part in zip(M, extra)]
    dict_budget = 0
    if "dictionary_budget" in w:
        from dictionary import item

        reference_cap = 2 * max(
            rec[0] for rec in struct.iter_unpack("<6I", records.read_bytes())
        )
        assert w["reference_classical"] == reference_cap and reference_cap >= 2 * (
            320975646 - w["reference_margin"]
        )
        for term in read(d / "extra_games.json"):
            weight = term["numerator"]
            assert type(weight) is int and weight >= 0
            add, cap = item(base, perms, term["atom"], len(M), m, center, reference_cap)
            assert cap == term["cap"]
            M = [[x + weight * v for x, v in zip(row, p)] for row, p in zip(M, add)]
            dict_budget += weight * cap
        assert dict_budget == w["dictionary_budget"]
    assert M == matrix(d / "matrix.txt")
    assert all(
        M[lift[i]][pb[j]] == sa[i] * sb[j] * v
        for lift, sa, pb, sb in perms
        for i, row in enumerate(M)
        for j, v in enumerate(row)
    )
    C = 320975646
    radius = w["reference_margin"]
    assert radius == 216000
    outside = 2 * t * (C - radius) + u * q * t / min(p)
    if w.get("comparison") == "column contractions":
        outside = 2 * mass * (C - radius) + u * q
    outside += game_budget + dict_budget
    assert (outside.numerator, outside.denominator) == (
        w["outside_numerator"],
        w["outside_denominator"],
    )
    X = w["alice_numerators"]
    Y = w["bob_numerators"]
    D = w["vector_denominator"]
    assert type(D) is int and D > 0
    assert (
        len(X) == len(M)
        and len(Y) == m
        and all(
            len(row) == 3 and all(type(t) is int for t in row) and dot(row, row) <= D * D
            for row in X + Y
        )
    )
    N = sum(t * dot(x, y) for row, x in zip(M, X) for t, y in zip(row, Y))
    assert N == w["quantum_numerator"]
    a = w["classical_alice_signs"]
    assert len(a) == len(M) and all(t in (-1, 1) for t in a)
    score = sum(abs(dot(a, col)) for col in zip(*M))
    assert score == w["attained"]
    if check_records:
        from packed_scores import Scores

        score_model, score_ref = Scores(M), Scores(center)
        highest = 0
        count = 0
        for rec in struct.iter_unpack("<6I", records.read_bytes()):
            mask = sum(v << (32 * i) for i, v in enumerate(rec[1:]))
            assert (
                mask < (1 << len(M)) and score_ref(mask) == 2 * rec[0] and rec[0] > C - radius
            )
            highest = max(highest, score_model(mask))
            count += 1
        assert highest == score and count == w["records"]
    assert max(F(score), outside) == F(
        w["classical_upper_numerator"], w["classical_upper_denominator"]
    )
    ratio = F(N, D**2) / max(F(score), outside)
    assert ratio > F(w["strict_lower_bound"])
    return w, M, center, ratio


def check_scores(root, w, records, solver):
    d = root / "second"
    report = subprocess.check_output(
        [
            str(solver),
            str(d / "matrix.txt"),
            str(records),
            str(d / "endpoint.txt"),
            str(320975646 - w["reference_margin"]),
        ],
        text=True,
    )
    data = json.loads(report)
    assert data["maximum"] == w["attained"] and data["count"] == w["records"]
    return data
