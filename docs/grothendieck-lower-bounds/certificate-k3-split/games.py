"""Reconstruct signed symmetry images of small games and prove their individual classical norms."""

import itertools


def changes(perms, terms, n, m):
    add = [[0] * m for _ in range(n)]
    total = 0
    for term in terms:
        weight = term["numerator"]
        assert type(weight) is int and weight >= 0
        if not weight:
            continue
        entries = term["entries"]
        assert entries and all(
            len(e) == 3 and all(type(t) is int for t in e) and 0 <= e[0] < n and 0 <= e[1] < m
            for e in entries
        )
        rows = sorted(set(i for i, j, x in entries))
        cols = sorted(set(j for i, j, x in entries))
        assert min(len(rows), len(cols)) <= 12
        if len(cols) < len(rows):
            A, B = cols, rows
            edge = [(j, i, z) for i, j, z in entries]
        else:
            A, B = rows, cols
            edge = entries
        pos = {x: i for i, x in enumerate(A)}
        col = {x: i for i, x in enumerate(B)}
        rr = [(pos[i], col[j], v) for i, j, v in edge]
        maximum = 0
        for tail in itertools.product((-1, 1), repeat=len(A) - 1):
            s = (1,) + tail
            y = [0] * len(B)
            for i, j, v in rr:
                y[j] += s[i] * v
            maximum = max(maximum, sum(map(abs, y)))
        assert maximum == term["classical"]
        total += weight * maximum * len(perms)
        for pa, sa, pb, sb in perms:
            for i, j, val in entries:
                add[pa[i]][pb[j]] += weight * val * sa[i] * sb[j]
    return add, total
