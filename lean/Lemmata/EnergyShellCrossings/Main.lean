module

public import Lemmata.EnergyShellCrossings.BalancedCrossing

@[expose] public section

set_option autoImplicit false

namespace Lemmata.EnergyShellCrossings

open Lemmata.FockCircuits

-- DOCS_BEGIN_MAIN
/-- Exact energy levels remove the mode coordinate from both crossing cuts. -/
theorem shellCrossingDecomposition (H E n m : ℕ) (hH : 0 < H)
    (hn : n ≤ partitionDimension (2 * H)) (hm : m ≤ partitionDimension (2 * E)) :
    IntegralShellCrossing H E n m :=
  EnergyShell.integral_shell_crossing H E n m hH hn hm

/-- A rectangular sum-of-squares identity with four terms per intermediate state. -/
theorem shellHurwitzBound (H E n m : ℕ) (hH : 0 < H)
    (hn : n ≤ partitionDimension (2 * H)) (hm : m ≤ partitionDimension (2 * E)) :
    ShellSumOfSquares H E n m :=
  EnergyShell.shell_sum_of_squares H E n m hH hn hm

/-- Balanced fusion has one rank coordinate per distinct transversal cut. -/
theorem balancedCrossingDecomposition (n : ℕ) (h : ℕ → ℕ)
    (hpos : ∀ r, 0 < h r)
    (hcapacity : ∀ r, BalancedCrossing.rankSequence n h r ≤ partitionDimension (2 * h r))
    (r : ℕ) : BalancedFusion n h r := by
  obtain ⟨p, hp, hroot⟩ := BalancedCrossing.balanced_decomposition n h hpos hcapacity r
  exact ⟨p, hp, hroot, BalancedCrossing.leaves_card r, BalancedCrossing.layouts_card r⟩
-- DOCS_END_MAIN

end Lemmata.EnergyShellCrossings
