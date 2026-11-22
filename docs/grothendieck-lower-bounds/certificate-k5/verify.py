"""Exact vector certificate for K_G(5), using the cited classical upper bound.

Uses only the Python standard library; an independent replay of Witness5.lean. It does
not prove the classical upper bound 919782264 of Marton et al., arXiv:2611.22893, Table 4.
The matrix and the vectors are read from lean/Lemmata/GrothendieckLowerBounds/Data5.lean.

    python verify.py [path/to/M80x269.txt]

With the published file (Examples/M80x269.txt of https://github.com/istvanmarton/IBB at
commit 6f17e2f073ccbe2de9cd0a7d062c25bff59ba844), the matrix is also compared with it entry
by entry.
"""
from pathlib import Path
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import sys
sys.dont_write_bytecode = True
import leandata  # noqa: E402

ROOT = Path(__file__).resolve().parent
PUBLISHED_SHA256 = "1db7786a6d256a36b50087f585fb85b76cfcdc715fd7df627a4de2b7098a968b"


def read_integer_matrix(path):
    rows = []
    for line in Path(path).read_text().splitlines():
        if not line.strip():
            continue
        row = [Decimal(s) for s in line.split()]
        assert all(x == x.to_integral_value() for x in row)
        rows.append([int(x) for x in row])
    return rows


def verify(published=None):
    record = json.loads((ROOT / "verification.json").read_text())
    M = leandata.table("Data5", "m5Rows")
    A = leandata.table("Data5", "a5Rows")
    B = leandata.table("Data5", "b5Rows")
    signs = leandata.row("Data5", "s5Row")
    # the matrix is M80x269 in normalized form: single spaces, a line feed after every row
    digest = hashlib.sha256(leandata.matrix_text(M).encode()).hexdigest()
    assert digest == record["matrix_sha256"]
    if published:
        assert hashlib.sha256(Path(published).read_bytes()).hexdigest() == PUBLISHED_SHA256
        assert read_integer_matrix(published) == M
        print("PASS: the matrix equals the published file entry by entry.")
    D = 10**15
    assert len(M) == len(A) == 80 and len(B) == 269
    assert all(len(row) == 269 for row in M)
    assert all(len(v) == 5 and sum(x*x for x in v) <= D*D for v in A + B)
    N = sum(M[i][j] * sum(A[i][k] * B[j][k] for k in range(5))
            for i in range(80) for j in range(269))
    assert N == record["q_exact_numerator"] == 1379089182810903048332452323838491520594
    assert record["q_exact_denominator"] == D*D
    C = record["classical_cited_upper"]
    assert C == 919782264 and len(signs) == 80 and all(x in (-1, 1) for x in signs)
    attained = sum(abs(sum(signs[i] * M[i][j] for i in range(80))) for j in range(269))
    assert attained == C
    ratio = Fraction(N, D*D*C)
    assert ratio > Fraction("1.49936483533988")
    with localcontext() as context:
        context.prec = 65
        print("Exact rational quotient:", Decimal(ratio.numerator) / Decimal(ratio.denominator))
    print("PASS: all 349 five-dimensional rational vectors satisfy the unit-ball constraints.")
    print("PASS: exact numerator, matrix identity, attaining classical signs, and strict quotient comparison.")
    print("K_G(5) > 1.49936483533988 using the cited classical upper bound C(M) <= 919782264.")
    print("The classical upper bound is an external result; it was not verified by this program.")


if __name__ == "__main__":
    verify(sys.argv[1] if len(sys.argv) > 1 else None)
