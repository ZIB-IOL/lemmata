"""Symmetrize embedded copies of the base and certify errors from integer rounding."""

_cached = None


def layout(perms, n, m):
    global _cached
    if _cached is not None and _cached[0] is perms:
        return _cached[1]

    def key(a, s, b, t):
        h = s[0]
        return (tuple(a), tuple(x * h for x in s), tuple(b), tuple(x * h for x in t))

    known = {key(a, s, b, t) for a, s, b, t in perms}
    assert len(known) == len(perms)
    for a, s, b, t in perms:
        for c, u, d, v in perms:
            assert (
                key(
                    [c[i] for i in a],
                    [x * u[i] for i, x in zip(a, s)],
                    [d[i] for i in b],
                    [x * v[i] for i, x in zip(b, t)],
                )
                in known
            )
    seen = set()
    orbits = []
    for i in range(n):
        for j in range(m):
            if (i, j) in seen:
                continue
            entries = {}
            conflict = False
            for a, s, b, t in perms:
                q = (a[i], b[j])
                v = s[i] * t[j]
                if q in entries and entries[q] != v:
                    conflict = True
                entries[q] = v
            assert (
                not (seen & entries.keys())
                and (i, j) in entries
                and len(perms) % len(entries) == 0
            )
            seen.update(entries)
            if not conflict:
                orbits.append([(x, y, v) for (x, y), v in entries.items()])
    _cached = (perms, orbits)
    return orbits


def embedded(base, perms, desc, n, m, classical=320975646):
    ia = desc["rows"]
    sa = desc["row_signs"]
    ib = desc["columns"]
    sb = desc["column_signs"]
    assert len(ia) == len(sa) == len(base) and len(ib) == len(sb) == len(base[0])
    assert all(type(i) is int and 0 <= i < n for i in ia) and all(
        type(j) is int and 0 <= j < m for j in ib
    )
    assert all(s in (-1, 1) for s in sa + sb)
    raw = [[0] * m for _ in range(n)]
    for ar, sg, row in zip(ia, sa, base):
        dest = raw[ar]
        for bc, t, v in zip(ib, sb, row):
            dest[bc] += sg * t * v
    ng = len(perms)
    rounded = [[0] * m for _ in range(n)]
    error = 0
    for orbit in layout(perms, n, m):
        h = len(orbit)
        numerator = sum(raw[i][j] * v for i, j, v in orbit)
        value = (1 if numerator >= 0 else -1) * ((abs(numerator) + h // 2) // h)
        for i, j, v in orbit:
            rounded[i][j] = v * value
        error += ng * abs(numerator - h * value)
    cap = classical + (error + ng - 1) // ng
    return rounded, cap


def item(base, perms, desc, n, m, reference=None, reference_cap=None):
    if desc["kind"] == "reference":
        assert reference is not None and reference_cap is not None
        return embedded(reference, perms, desc, n, m, reference_cap)
    if desc["kind"] == "base":
        return embedded(base, perms, desc, n, m)
    assert desc["kind"] == "small"
    from games import changes

    return changes(
        perms, [dict(numerator=1, entries=desc["entries"], classical=desc["classical"])], n, m
    )
