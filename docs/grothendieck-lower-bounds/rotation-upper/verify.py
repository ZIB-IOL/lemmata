"""Exact arithmetic for the rotation bound. Pass the original Julia supplement to compare inputs."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path
import re


def integer(digits):
    # The published error has more digits than Python's default int(string) limit.
    value = 0
    for start in range(0, len(digits), 9):
        group = digits[start:start + 9]
        if not group.isascii() or not group.isdigit():
            raise ValueError("expected unsigned decimal digits")
        value = value * 10**len(group) + int(group)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("supplement", nargs="?", type=Path)
    args = parser.parse_args()
    pairs = json.loads(Path(__file__).with_name("inputs.json").read_text())["rationals"]
    if args.supplement:
        source = args.supplement.read_text(encoding="utf-8")
        for key, symbol in [("eta_squared", "η²"), ("upsilon", "υ"), ("v0", "v₀")]:
            match = re.search(r"^" + symbol + r" = ([0-9]+)//([0-9]+)$", source, re.M)
            if not match or list(match.groups()) != pairs[key]:
                raise ValueError(f"{symbol} differs from its published value")

    eta2, upsilon, v0 = [F(*map(integer, pairs[k])) for k in ("eta_squared", "upsilon", "v0")]
    h = F("0.9967561175483381")
    w = F("0.6919401772871383")
    assert 0 < h <= 1 and h*h <= eta2 <= 1
    assert 0 < w < v0 and 0 <= upsilon and w*w*upsilon <= (v0-w)**2

    # Old upper endpoint U satisfies (U eta² v0 - 1)² = upsilon on the positive branch.
    lo = F("1.45463365671869294") * eta2*v0 - 1
    hi = F("1.45463365671869295") * eta2*v0 - 1
    assert 0 < lo < hi and lo**2 < upsilon < hi**2

    a, b, delta = F(19, 20), (1+h)/2, (1-h)/2
    r = h + h**3 * (1-h)/4
    s2 = 1 - 2*a*h + a*a
    scale = 10**20
    s_upper = F(1 + isqrt((scale**2 * s2.numerator) // s2.denominator), scale)
    assert 0 < s_upper and s2 <= s_upper**2
    lam = b*b + a*(r-b) - s_upper*delta
    uniform = F("1.4512635753")
    assert w*lam*uniform >= 1
    assert uniform < F("1.451263576")
    with localcontext() as ctx:
        ctx.prec = 36
        upper = 1/(w*lam)
        print("Rationally certified rotation upper endpoint (display rounded):",
              Decimal(upper.numerator)/Decimal(upper.denominator))
    print("Certified strict inequality: K_G(3) < 1.451263576")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Use Python without -O to enable the checks.")
    main()
