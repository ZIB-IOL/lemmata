"""Optional exact SDP bound for this fixed matrix, using only Python integers.

This is not an upper bound on the Grothendieck constant. The attaining classical
assignment suffices for the denominator in the fixed-matrix ratio upper bound.
The matrix and the signs are read from lean/Lemmata/GrothendieckLowerBounds/Data5.lean.
"""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal, localcontext
import hashlib
import json
import sys
sys.dont_write_bytecode = True
import leandata  # noqa: E402

ROOT = Path(__file__).resolve().parent
w = json.loads((ROOT / "dual.json").read_text())
M = leandata.table("Data5", "m5Rows")
assert hashlib.sha256(leandata.matrix_text(M).encode()).hexdigest() == w["matrix_sha256"]
n, m = len(M), len(M[0]); N = n + m
F, D = w["diagonal_denominator"], w["factor_denominator"]; scale = D*D
assert scale % F == 0 and scale % 2 == 0
R = w["factor_numerators"]; y = w["diagonal_numerators"]
assert len(R) == len(y) == N and all(len(row) == N for row in R)
assert all(type(x) is int for row in R for x in row) and all(type(x) is int for x in y)
columns = list(zip(*R)); row_sums = [0]*N
for i in range(N):
    for j in range(i, N):
        residual = -sum(x*z for x, z in zip(columns[i], columns[j]))
        if i == j: residual += y[i]*(scale//F)
        if i < n <= j: residual -= M[i][j-n]*(scale//2)
        row_sums[i] += abs(residual)
        if i != j: row_sums[j] += abs(residual)
eta = max(row_sums)
upper = Fraction(sum(y), F) + N*Fraction(eta, scale)
a = leandata.row("Data5", "s5Row")
assert len(a) == n and all(s in (-1, 1) for s in a)
attained = sum(abs(sum(a[i]*M[i][j] for i in range(n))) for j in range(m))
assert attained == 919782264
expected = Fraction(689544591405532440504120517535361, 500000000000000000000000)
assert upper == expected
with localcontext() as context:
    context.prec = 60
    print("Q_infinity(M) upper bound:", Decimal(upper.numerator)/Decimal(upper.denominator))
    ratio = upper/attained
    print("Fixed-matrix Q_infinity(M)/C(M) upper bound:", Decimal(ratio.numerator)/Decimal(ratio.denominator))
assert upper/attained < Fraction("1.49936483534006")
print("PASS: exact rational PSD residual certificate; this is not a global K_G upper bound.")
