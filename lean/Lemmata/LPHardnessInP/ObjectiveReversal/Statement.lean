module

public import Lemmata.SpanningTreeMinSplit.Main

@[expose] public section

namespace Lemmata.LPHardnessInP.ObjectiveReversal

/-- A maximization-to-minimization reduction with maps independent of the instance.
The completion map may replace a target solution by an encoded source solution
of no greater cost. -/
structure Reversal {I S T : Type*} (value : I → S → ℝ) (cost : I → T → ℝ)
    (baseline : I → ℝ) where
  encode : S → T
  complete : T → S
  objective_identity : ∀ i s, cost i (encode s) = baseline i - value i s
  completion_dominates : ∀ i t, cost i (encode (complete t)) ≤ cost i t

/-- A concrete formulation of optimum preservation, including attainment. -/
def OptimumTransfer : Prop :=
  ∀ {I S T : Type*} {value : I → S → ℝ} {cost : I → T → ℝ}
    {baseline : I → ℝ} (_D : Reversal value cost baseline) (i : I) (opt : ℝ),
    (∀ s, value i s ≤ opt) → (∃ s, value i s = opt) →
    (∀ t, baseline i - opt ≤ cost i t) ∧
      ∃ t, cost i t = baseline i - opt

/-- The nonnegative row offset in the near-exact edge-cover transfer. -/
noncomputable def reversalOffset (N C opt : ℝ) : ℝ :=
  C - opt - (1 - 1 / (1 + 1 / (4 * N))) * (N - opt)

end Lemmata.LPHardnessInP.ObjectiveReversal
