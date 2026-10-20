module

public import Lemmata.LPHardnessInP.ParityExtension.Extension
public import Lemmata.LPHardnessInP.ParityExtension.Sampling
public import Lemmata.LPHardnessInP.ParityExtension.Parameters
public import Lemmata.LPHardnessInP.ParityExtension.Goodness
public import Lemmata.LPHardnessInP.ParityExtension.Padding
public import Lemmata.LPHardnessInP.ParityExtension.ConcreteData

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open Lemmata.SpanningTreeMinSplit
open Lemmata.LPHardnessInP.Parity

-- DOCS_BEGIN_MAIN
/-- A calibrated finite form of the shifted parity-rank extension. The
entropy and partition assertions are explicit finite JSY data; the new
charge, signed witness, and numerical parameter choice are proved. -/
theorem calibrated_shifted_rank_from_jsy
    {I J H Ω : Type*} [Fintype I] [Fintype J]
    [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Ω]
    (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (t : I → J → ℝ)
    {k L : ℕ} {smallError badError U r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hk : 400 / r ≤ (k : ℝ))
    (hcard : Fintype.card H = (2 * k + 3).choose 3)
    (hs : 0 ≤ smallError) (hb : 0 ≤ badError)
    (h₃ : SupportedAt μ₃ t 3)
    (hₕ : SupportedAt μₕ t (4 * (k : ℝ) + 3))
    (h₁ : SupportedAt μ₁ t 1)
    (data : ∀ R : Finset I, ∀ C : Finset J,
      JSYRectangleData H Ω (10 * k) (r / 100)
        (rectangleMass μ₃ R C) (rectangleMass μₕ R C) (rectangleMass μ₁ R C)
        smallError badError)
    (hU : 0 ≤ U) (hupper : ∀ i j, t i j - r ≤ U)
    (hthreshold : ((L : ℝ) - 1) * ((smallError + badError) / (1 - r / 100)) * U ≤
      3 * r / 2) :
    (L : ℕ∞) ≤ nonnegativeRank (fun i j => t i j - r) := by
  apply shifted_rank_lower_bound_from_jsy μ₃ μₕ μ₁ t
    (by positivity) (by linarith) hs hb h₃ hₕ h₁ data hU hupper
  have hgap := hthreshold.trans_lt (calibrated_witness_gap hr hr1 hk)
  simpa [parityCoefficientA, parityCoefficientB, hcard] using hgap

/-- The new extension feeds directly into the actual odd-red matching LP
lower bound. The rank bound and the finite corruption inequality are both
derived from the displayed partition/goodness hypotheses. -/
theorem parity_lp_lower_bound_from_jsy
    {n m L : ℕ} {V H Ω : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Ω]
    (hn : 0 < n) (α : ℝ) (hα : 1 < α)
    (C : Lemmata.LPHardnessInP.Formulation.CertifiedLP (V := V)
      (fun (a : ParityLabel n) M => matchingCost a (2 * (α - 1) * n) M)
      (fun _ => ((n : ℝ) + 2 * (α - 1) * n) / α) m)
    (μ₃ μₕ μ₁ : ProbabilityMatrix (ParityLabel n) (ParityMatching n))
    {k : ℕ} {smallError badError : ℝ}
    (hk : 400 / (1 / (2 * α)) ≤ (k : ℝ))
    (hcard : Fintype.card H = (2 * k + 3).choose 3)
    (hs : 0 ≤ smallError) (hb : 0 ≤ badError)
    (h₃ : SupportedAt μ₃ (fun a M => (violationCount a M : ℝ)) 3)
    (hₕ : SupportedAt μₕ (fun a M => (violationCount a M : ℝ)) (4 * (k : ℝ) + 3))
    (h₁ : SupportedAt μ₁ (fun a M => (violationCount a M : ℝ)) 1)
    (data : ∀ R : Finset (ParityLabel n), ∀ T : Finset (ParityMatching n),
      ConcreteJSYRectangleData H Ω (4 * k + 3) (10 * k) ((1 / (2 * α)) / 100)
        (rectangleMass μ₃ R T) (rectangleMass μₕ R T) (rectangleMass μ₁ R T)
        smallError badError)
    (hthreshold : ((L : ℝ) - 1) *
      ((smallError + badError) / (1 - (1 / (2 * α)) / 100)) * n ≤
        3 * (1 / (2 * α)) / 2) :
    L ≤ m + 1 := by
  have hr : 0 < 1 / (2 * α) := by positivity
  have hr1 : 1 / (2 * α) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  apply parity_matching_lp_lower_bound hn α hα C
  apply calibrated_shifted_rank_from_jsy μ₃ μₕ μ₁ _
    hr hr1 hk hcard hs hb h₃ hₕ h₁
    (fun R T => (data R T).toJSYRectangleData) (Nat.cast_nonneg n) ?_ hthreshold
  intro a M
  have ht : (violationCount a M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast violationCount_le_order a M
  linarith
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.ParityExtension
