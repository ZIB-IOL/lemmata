"""Bound the improvement from optimizing either player's triples with the other fixed."""

from fractions import Fraction
from math import isqrt


def interval(matrix, fixed, vector_denominator):
    # The optimal free triple is parallel to the weighted sum of the fixed triples.
    precision = 10**22
    lower = 0
    for row in matrix:
        field = [sum(c * v[k] for c, v in zip(row, fixed)) for k in range(3)]
        lower += isqrt(sum(x * x for x in field) * precision**2)
    scale = vector_denominator * precision
    return Fraction(lower, scale), Fraction(lower + len(matrix), scale)


def bounds(matrix, witness):
    D = witness["vector_denominator"]
    C = Fraction(witness["classical_upper_numerator"], witness["classical_upper_denominator"])
    current = Fraction(witness["quantum_numerator"], D**2) / C
    free_rows = interval(matrix, witness["bob_numerators"], D)
    free_columns = interval(list(zip(*matrix)), witness["alice_numerators"], D)
    ans = {}
    for name, pair in [("alice", free_rows), ("bob", free_columns)]:
        upper = pair[1] / C - current
        assert upper >= 0
        ans[name] = {
            "gain_upper_numerator": upper.numerator,
            "gain_upper_denominator": upper.denominator,
        }
    return ans
