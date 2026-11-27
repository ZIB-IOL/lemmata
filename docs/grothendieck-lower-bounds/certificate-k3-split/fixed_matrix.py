"""Refine unit triples with integers and bound the vector optimum in every dimension."""

from fractions import Fraction
from math import isqrt
from band_certificate import norm_square


def fields(matrix, vectors):
    coordinates = list(zip(*vectors))
    return [
        tuple(sum(a * b for a, b in zip(row, axis)) for axis in coordinates) for row in matrix
    ]


def length_up(row):
    square = sum(x * x for x in row)
    root = isqrt(square)
    return root + (root * root < square)


def triples(values, denominator):
    result = []
    for row in values:
        length = length_up(row)
        result.append(
            [((x >= 0) - (x < 0)) * (abs(x) * denominator // length) for x in row]
            if length
            else [denominator, 0, 0]
        )
    return result


def refine(matrix, start, denominator=10**36, steps=96):
    transpose = list(zip(*matrix))
    alice = triples(start, denominator)
    best = None
    for i in range(steps):
        bob = triples(fields(transpose, alice), denominator)
        field = fields(matrix, bob)
        new_alice = triples(field, denominator)
        score = sum(sum(x * y for x, y in zip(a, b)) for a, b in zip(new_alice, field))
        if best is None or score > best[0]:
            best = (score, new_alice, bob)
        if new_alice == alice:
            break
        alice = new_alice
    return best


def lower_factor(gram, diagonal):
    # Round a Cholesky factor using integer recurrences. The subsequent proof
    # charges the entire residual, including each rounding error.
    factor = []
    error = 0
    for i, row in enumerate(gram):
        current = []
        for j, past in enumerate(factor):
            residual = -row[j] - sum(a * b for a, b in zip(current, past))
            pivot = past[-1]
            rounded = (residual + pivot // 2) // pivot
            error += 2 * abs(residual - rounded * pivot)
            current.append(rounded)
        residual = diagonal[i] - row[i] - sum(v * v for v in current)
        if residual < 1:
            raise ArithmeticError("Increase the diagonal margin")
        pivot = isqrt(residual)
        error += residual - pivot * pivot
        current.append(pivot)
        factor.append(current)
    return factor, error


def propose(matrix, x, y, denominator):
    scale = 10**68
    row_fields = list(map(length_up, fields(matrix, y)))
    column_fields = list(map(length_up, fields(list(zip(*matrix)), x)))
    weights = [scale * denominator // v for v in column_fields]
    weighted = [[a * b for a, b in zip(row, weights)] for row in matrix]
    gram = [
        [sum(x * y for x, y in zip(row, z)) for z in matrix[: i + 1]]
        for i, row in enumerate(weighted)
    ]
    for power in (34, 31, 28, 24, 20, 16, 12, 8):
        h = 10**power
        diagonal = [
            (scale * v * (h + 1) + denominator * h - 1) // (denominator * h) for v in row_fields
        ]
        try:
            factor, error = lower_factor(gram, diagonal)
        except ArithmeticError:
            continue
        cert = dict(
            reciprocals=weights,
            diagonal=diagonal,
            lower_triangular=factor,
            error=error,
            precision=10**25,
        )
        square = norm_square(matrix, cert)
        precision = cert["precision"]
        cert["vector_upper_numerator"] = (
            isqrt(square.numerator * precision**2 // square.denominator) + 1
        )
        return cert
    raise ArithmeticError("No positive rounding margin was found")


def bound(matrix, cert, classical):
    square = norm_square(matrix, cert)
    precision = cert["precision"]
    assert type(precision) is int and precision > 0 and classical > 0
    upper = isqrt(square.numerator * precision**2 // square.denominator) + 1
    assert upper == cert["vector_upper_numerator"]
    return Fraction(upper, precision * classical)
