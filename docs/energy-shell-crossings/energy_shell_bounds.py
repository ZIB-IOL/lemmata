#!/usr/bin/env python3
"""Compare finite crossing certificates using exact integer partition counts.

This computes bounds, not optimal ranks. The Lean proofs are in
Lemmata/EnergyShellCrossings/EnergyShellCrossing.lean and BalancedCrossing.lean.
Run: python3 docs/energy-shell-crossings/energy_shell_bounds.py
"""

import argparse
import itertools
import math


def partition_counts(limit):
    """Coefficient of z^k in product_(j>=0) (1 + z^(2j+1))."""
    counts = [1] + [0] * limit
    for part in range(1, limit + 1, 2):
        for total in range(limit, part - 1, -1):
            counts[total] += counts[total - part]
    return counts


def first_capacity(values, target, start=0):
    for index in range(start, len(values)):
        if values[index] >= target:
            return index
    raise ValueError("Increase --limit to include the required energy level")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=8192,
                        help="maximum doubled energy in the partition table")
    args = parser.parse_args()
    if args.limit < 20:
        parser.error("--limit must be at least 20")
    counts = partition_counts(args.limit)
    # Independently enumerate the small states to catch normalization mistakes.
    brute = [0] * 21
    for bits in itertools.product((0, 1), repeat=10):
        energy = sum(bit * (2 * j + 1) for j, bit in enumerate(bits))
        if energy <= 20:
            brute[energy] += 1
    assert counts[:21] == brute
    prefix = list(itertools.accumulate(counts))
    shells = counts[::2]
    cumulative = prefix[::2]

    def q(energy):
        if energy >= len(cumulative):
            raise ValueError("Increase --limit for the intermediate cutoff")
        return cumulative[energy]

    print("Finite complex sum-of-squares upper bounds; all capacities are exact.")
    print(" log2(n)   H_old   E_old   h_shell   log2(old)   log2(shell)   old/shell")
    for power in (8, 16, 32, 64):
        n = 2 ** power
        old_h = next((h for h in range(1, len(cumulative))
                      if cumulative[h] > 2 * h * n), None)
        if old_h is None:
            raise ValueError("Increase --limit for the old capacity condition")
        old_e = first_capacity(cumulative, n)
        shell_h = first_capacity(shells, n, start=1)
        old = 8 * old_h * q(old_h + old_e)
        new = 4 * q(2 * shell_h)
        print(f"{power:8d} {old_h:7d} {old_e:7d} {shell_h:9d}"
              f" {math.log2(old):11.3f} {math.log2(new):13.3f} {old / new:11.1f}")

    print("\nBalanced fusion with n = 2^16; rank is per cut, not summed over cuts.")
    print(" wires   layouts(log2)   rank(log2)   next_shell")
    rank = 2 ** 16
    for level in range(5):
        shell_h = first_capacity(shells, rank, start=1)
        wires = 2 ** level
        print(f"{wires:6d} {wires - 1:15d} {math.log2(rank):12.3f} {shell_h:12d}")
        if level < 4:
            rank = q(2 * shell_h)


if __name__ == "__main__":
    main()
