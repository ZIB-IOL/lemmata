module

public import Lemmata.MatchingCostTransfer.Statement
public import Lemmata.NonnegativeRankReduction.Main
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.MatchingCostTransfer

open Lemmata.SpanningTreeMinSplit
open Lemmata.NonnegativeRankReduction
open scoped BigOperators

-- DOCS_BEGIN_MAIN
/-- Positive baseline costs produce a constant shifted violation matrix. -/
theorem positive_cost_identity : PositiveCostIdentity := by
  intro α H q hα
  have hα0 : α ≠ 0 := by linarith
  field_simp
  ring

/-- The scaling used in the positive-cost construction is strictly positive. -/
theorem positive_cost_scale {α H : ℝ} (hα : 1 < α) (hH : 0 < H) :
    0 < 2 * (α - 1) * H := by positivity

/-- Summing baseline-one costs gives the solution cardinality plus the
crossing penalty times the number of violations. -/
theorem sum_positive_cost {E : Type*} (M : Finset E) (p : E → Prop)
    [DecidablePred p] (γ : ℝ) :
    (∑ e ∈ M, (1 + if p e then γ else 0)) =
      (M.card : ℝ) + γ * ((M.filter p).card : ℝ) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  simp [mul_comm]

/-- A bounded additive baseline leaves a positive shift. -/
theorem retainedShift_pos {α B : ℝ} (hα : 1 < α)
    (hB : B < 1 / (α - 1)) : 0 < retainedShift α B := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have hmul : B * (α - 1) < 1 := (lt_div_iff₀ hα1).mp hB
  unfold retainedShift
  exact div_pos (by nlinarith) hα0

/-- When the baseline bound is nonnegative, the retained shift is at most
`1 / α` and therefore strictly below one. -/
theorem retainedShift_lt_one {α B : ℝ} (hα : 1 < α) (hB : 0 ≤ B) :
    retainedShift α B < 1 := by
  have hα0 : 0 < α := by linarith
  have hmul : 0 ≤ (α - 1) * B := mul_nonneg (by linarith) hB
  unfold retainedShift
  apply (div_lt_iff₀ hα0).mpr
  linarith

/-- The correction from a row-dependent shift to a uniform shift is a
nonnegative row constant. -/
theorem baseline_correction_nonneg {α B a b : ℝ} (hα : 1 < α)
    (hbase : b / a ≤ B) :
    0 ≤ (α - 1) * (B - b / a) / α :=
  div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hbase)) (by linarith)

/-- Exact reduction identity, before applying nonnegative factorization. -/
theorem baseline_reduction_identity {α a : ℝ} (hα : α ≠ 0) (ha : a ≠ 0)
    (B b q : ℝ) :
    (1 / a) * (a * q + b - (a + b) / α) +
        (α - 1) * (B - b / a) / α =
      q - retainedShift α B := by
  unfold retainedShift
  field_simp
  ring

/-- The positive-cost slack and the fixed-shift source have exactly the same
nonnegative rank. No source rank lower bound is assumed or proved here. -/
theorem positive_cost_rank_identity : PositiveCostRankIdentity := by
  intro I J q α H hα hH
  have hid :
      costSlack q (fun _ => 2 * (α - 1) * H) (fun _ => H) α =
        (fun i j => (2 * (α - 1) * H) * (q i j - 1 / (2 * α))) := by
    funext i j
    simpa only [costSlack, add_comm] using positive_cost_identity α H (q i j) hα
  rw [hid]
  exact rank_rowScale_eq _ _ (fun _ => positive_cost_scale hα hH)

/-- Construct the factorization used by the bounded-baseline reduction. -/
noncomputable def boundedBaselineFactorization {I J : Type*}
    (q : I → J → ℝ) (a b : I → ℝ) (α B : ℝ) {k : ℕ}
    (hα : 1 < α) (ha : ∀ i, 0 < a i) (hbase : ∀ i, b i / a i ≤ B)
    (F : NonnegativeFactorization (costSlack q a b α) k) :
    NonnegativeFactorization (fun i j => q i j - retainedShift α B) (k + 1) := by
  let G := factorRowScale F (fun i => 1 / a i)
    (fun i => one_div_nonneg.mpr (ha i).le)
  let K := factorRowOffset G (fun i => (α - 1) * (B - b i / a i) / α)
    (fun i => baseline_correction_nonneg hα (hbase i))
  have hid :
      (fun i j => (1 / a i) * costSlack q a b α i j +
        (α - 1) * (B - b i / a i) / α) =
        (fun i j => q i j - retainedShift α B) := by
    funext i j
    exact baseline_reduction_identity (by linarith) (ne_of_gt (ha i)) B (b i) (q i j)
  rw [← hid]
  exact K

/-- The factorization form of the bounded-baseline transfer theorem. -/
theorem bounded_baseline_transfer : BoundedBaselineTransfer := by
  intro I J q a b α B k hα ha hbase F
  exact ⟨boundedBaselineFactorization q a b α B hα ha hbase F⟩

/-- The useful parameter range of the baseline reduction, with the strict
source-shift bounds and the factorization transfer in one statement. -/
theorem bounded_baseline_positive_transfer {I J : Type*}
    (q : I → J → ℝ) (a b : I → ℝ) (α B : ℝ) {k : ℕ}
    (hα : 1 < α) (ha : ∀ i, 0 < a i) (hbase : ∀ i, b i / a i ≤ B)
    (hB0 : 0 ≤ B) (hB : B < 1 / (α - 1))
    (F : NonnegativeFactorization (costSlack q a b α) k) :
    0 < retainedShift α B ∧ retainedShift α B < 1 ∧
      Nonempty (NonnegativeFactorization
        (fun i j => q i j - retainedShift α B) (k + 1)) :=
  ⟨retainedShift_pos hα hB, retainedShift_lt_one hα hB0,
    bounded_baseline_transfer q a b α B k hα ha hbase F⟩

/-- Plug any source nonnegative-rank lower bound into the bounded-baseline
reduction. The source lower bound is an explicit hypothesis. -/
theorem bounded_baseline_lower_bound {I J : Type*}
    (q : I → J → ℝ) (a b : I → ℝ) (α B : ℝ) {k L : ℕ}
    (hα : 1 < α) (ha : ∀ i, 0 < a i) (hbase : ∀ i, b i / a i ≤ B)
    (hsource : (L : ℕ∞) ≤ nonnegativeRank (fun i j => q i j - retainedShift α B))
    (F : NonnegativeFactorization (costSlack q a b α) k) :
    L ≤ k + 1 := by
  have h := hsource.trans
    (nonnegativeRank_le (boundedBaselineFactorization q a b α B hα ha hbase F))
  exact_mod_cast h

/-- The constant positive-cost construction transfers a source lower bound
without an additional factor. -/
theorem positive_cost_lower_bound {I J : Type*}
    (q : I → J → ℝ) (α H : ℝ) {k L : ℕ} (hα : 1 < α) (hH : 0 < H)
    (hsource : (L : ℕ∞) ≤ nonnegativeRank (fun i j => q i j - 1 / (2 * α)))
    (F : NonnegativeFactorization
      (costSlack q (fun _ => 2 * (α - 1) * H) (fun _ => H) α) k) :
    L ≤ k := by
  rw [← positive_cost_rank_identity q α H hα hH] at hsource
  exact_mod_cast hsource.trans (nonnegativeRank_le F)

/-- Exchanging instances and solutions preserves the rank of the shifted
violation matrix, as used in the odd-cut transfer. -/
theorem transposed_shift_rank {I J : Type*} (q : I → J → ℝ) (r : ℝ) :
    nonnegativeRank (fun j i => q i j - r) =
      nonnegativeRank (fun i j => q i j - r) :=
  rank_transpose _

/-- A row minimum of one in `q` gives the minimum `a + b` under
nonnegative increasing costs. -/
theorem transformed_row_minimum {J : Type*} (q : J → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hq : ∀ j, 1 ≤ q j) (hattain : ∃ j, q j = 1) :
    (∀ j, a + b ≤ a * q j + b) ∧
      (∃ j, a * q j + b = a + b) := by
  constructor
  · intro j
    have h := mul_le_mul_of_nonneg_left (hq j) ha
    linarith
  · obtain ⟨j, hj⟩ := hattain
    exact ⟨j, by rw [hj]; ring⟩

/-- The positive costs used in the matching reduction are metrics. -/
theorem cut_metric_properties : CutMetricProperties := by
  intro V inst side γ hγ
  constructor
  · intro u
    simp [cutMetric]
  constructor
  · intro u v
    simp [cutMetric, eq_comm]
  constructor
  · intro u v huv
    simp only [cutMetric, ite_eq_right huv]
    split_ifs <;> linarith
  · intro u v w
    by_cases huv : u = v
    · subst v
      simp [cutMetric]
    by_cases hvw : v = w
    · subst w
      simp [cutMetric]
    by_cases huw : u = w
    · subst w
      simp only [cutMetric, ite_eq_right huv, ite_eq_right (Ne.symm huv)]
      split_ifs <;> linarith
    simp only [cutMetric, ite_eq_right huv, ite_eq_right hvw, ite_eq_right huw]
    by_cases huv' : side u = side v
    · by_cases hvw' : side v = side w
      · simp [huv', hvw']
      · have huw' : side u ≠ side w := by
          intro h
          exact hvw' (huv'.symm.trans h)
        simp [huv', hvw']
    · by_cases hvw' : side v = side w
      · have huw' : side u ≠ side w := by
          intro h
          exact huv' (h.trans hvw'.symm)
        simp [hvw', huw']
      · simp only [ite_eq_right huv', ite_eq_right hvw']
        split_ifs <;> linarith
-- DOCS_END_MAIN

end Lemmata.MatchingCostTransfer
