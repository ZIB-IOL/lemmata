"""Check the explicit rank-three witness using Python integers only.

An independent replay of the checks in Witness3.lean: unit-ball constraints, the exact
numerator, and an attaining classical assignment. The global classical upper bound is
established separately by verify_classical.cpp.
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
NUMERATOR = 461845159210737970564046146266219485493
DENOMINATOR = 10**30
CLASSICAL = 320975296
LOWER = Fraction("1.43888070193021")


def verify():
    matrix = leandata.table("Data3", "m3Rows")
    alice = leandata.table("Data3", "a3Rows")
    bob = leandata.table("Data3", "b3Rows")
    signs = leandata.row("Data3", "s3Row")
    recorded = json.loads((ROOT / "provenance.json").read_text())["matrix_sha256"]
    digest = hashlib.sha256(leandata.matrix_text(matrix).encode()).hexdigest()
    assert digest == recorded
    denominator = 10**15
    assert len(matrix) == len(alice) == 81
    assert len(bob) == 321 and all(len(row) == 321 for row in matrix)
    assert all(len(v) == 3 and sum(x*x for x in v) <= denominator**2 for v in alice + bob)
    numerator = sum(matrix[i][j] * sum(alice[i][k] * bob[j][k]
                    for k in range(3)) for i in range(81) for j in range(321))
    assert numerator == NUMERATOR and denominator**2 == DENOMINATOR
    assert len(signs) == 81 and all(x in (-1, 1) for x in signs)
    attained = sum(abs(sum(signs[i] * matrix[i][j] for i in range(81)))
                   for j in range(321))
    assert attained == CLASSICAL
    ratio = Fraction(numerator, denominator**2 * CLASSICAL)
    assert ratio > LOWER
    with localcontext() as context:
        context.prec = 60
        decimal = str(Decimal(ratio.numerator) / Decimal(ratio.denominator))
    result = {
        "matrix_shape": [81, 321],
        "matrix_sha256": digest,
        "unit_ball_constraints": "all 402 checked exactly in dimension 3",
        "quantum_numerator": numerator,
        "quantum_denominator": denominator**2,
        "classical_value_attained": attained,
        "ratio_decimal": decimal,
        "strict_decimal_lower_bound": "1.43888070193021",
        "global_classical_upper_bound": "requires separate C++ search",
    }
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    verify()
