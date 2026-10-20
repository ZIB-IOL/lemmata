module

public import Lemmata.SpanningTreeMinSplit.Main

@[expose] public section

namespace Lemmata.LPHardnessInP.CostTransfer

open Lemmata.SpanningTreeMinSplit

/-- The approximation slack of the costs `a i * q i j + b i`, when the
minimum in row `i` is `a i + b i`. The asserted minimum is a separate
application-specific fact, not an assumption hidden in this definition. -/
noncomputable def costSlack {I J : Type*} (q : I → J → ℝ) (a b : I → ℝ) (α : ℝ) :
    I → J → ℝ :=
  fun i j => a i * q i j + b i - (a i + b i) / α

/-- The constant shift retained by a uniform bound on the additive baseline. -/
noncomputable def retainedShift (α B : ℝ) : ℝ :=
  (1 - (α - 1) * B) / α

/-- The exact scalar slack identity used for the positive-cost matching
construction. It applies to any real violation count `q`. -/
def PositiveCostIdentity : Prop :=
  ∀ (α H q : ℝ), 1 < α →
    H + (2 * (α - 1) * H) * q - (H + 2 * (α - 1) * H) / α =
      (2 * (α - 1) * H) * (q - 1 / (2 * α))

/-- The positive-cost transformation preserves the nonnegative rank of the
constant-shift source matrix. -/
def PositiveCostRankIdentity : Prop :=
  ∀ {I J : Type*} (q : I → J → ℝ) (α H : ℝ), 1 < α → 0 < H →
    nonnegativeRank
        (costSlack q (fun _ => 2 * (α - 1) * H) (fun _ => H) α) =
      nonnegativeRank (fun i j => q i j - 1 / (2 * α))

/-- A uniform bound on the baseline ratio transfers a target factorization to
the constant-shift source using at most one additional factor. -/
def BoundedBaselineTransfer : Prop :=
  ∀ {I J : Type*} (q : I → J → ℝ) (a b : I → ℝ) (α B : ℝ) (k : ℕ),
    1 < α → (∀ i, 0 < a i) → (∀ i, b i / a i ≤ B) →
    NonnegativeFactorization (costSlack q a b α) k →
    Nonempty (NonnegativeFactorization
      (fun i j => q i j - retainedShift α B) (k + 1))

/-- A two-cluster metric: zero on the diagonal, one within a cluster, and
`1 + γ` between clusters. -/
noncomputable def cutMetric {V : Type*} [DecidableEq V] (side : V → Bool) (γ : ℝ)
    (u v : V) : ℝ :=
  if u = v then 0 else 1 + if side u = side v then 0 else γ

/-- The ordinary metric axioms, including strict positivity off the diagonal,
for the two-cluster cost construction. -/
def CutMetricProperties : Prop :=
  ∀ {V : Type*} [DecidableEq V] (side : V → Bool) (γ : ℝ), 0 ≤ γ →
    (∀ u, cutMetric side γ u u = 0) ∧
    (∀ u v, cutMetric side γ u v = cutMetric side γ v u) ∧
    (∀ u v, u ≠ v → 0 < cutMetric side γ u v) ∧
    (∀ u v w, cutMetric side γ u w ≤
      cutMetric side γ u v + cutMetric side γ v w)

end Lemmata.LPHardnessInP.CostTransfer
