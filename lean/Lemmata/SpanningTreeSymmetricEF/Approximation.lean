module

/-
  Formal arithmetic and finite-function statements for approximation.

  Scope: this module proves closed-form marginal identities, the nonnegative
  label-event inequalities, and the approximation-factor implication for an
  actual point in an actual outer relaxation. It does not enumerate Hamilton
  paths or prove their alternating-stabilizer orbit theorem. Membership of the
  signed point is an explicit geometric input, not an unrestricted axiom.
-/
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.Approximation

open scoped BigOperators
noncomputable section

/-- Closed-form normalization after the cycle-incidence counts are substituted.
The combinatorial derivation of those counts is not asserted by this lemma. -/
theorem path_normalization_arithmetic (n : ℝ) (hn : 6 ≤ n) :
    3 / (n * (n - 4)) *
      (n * (n - 2) - 4 / (n - 2) * (n * (n - 1) * (n - 2) / 6)) = 1 := by
  have h0 : n ≠ 0 := by linarith
  have h2 : n - 2 ≠ 0 := by linarith
  have h4 : n - 4 ≠ 0 := by linarith
  field_simp
  ring

/-- The one-position and adjacent/nonadjacent two-position closed formulas.
This covers their algebra, not counting the labelled orderings. -/
theorem path_marginal_arithmetic (n : ℝ) (hn : 6 ≤ n) :
    (3 / (n * (n - 4)) *
      (3 * (n - 2) - 4 / (n - 2) * ((n - 1) * (n - 2) / 2)) = 3 / n) ∧
    (3 / (n * (n - 4)) * (n - 4 / (n - 2) * (n - 2)) = 3 / n) ∧
    (3 / (n * (n - 4)) * (4 - 4 / (n - 2) * (n - 2)) = 0) := by
  have h0 : n ≠ 0 := by linarith
  have h2 : n - 2 ≠ 0 := by linarith
  have h4 : n - 4 ≠ 0 := by linarith
  constructor
  · field_simp
    ring
  constructor
  · field_simp
  · field_simp
    ring

/-- Nonnegativity of the SS, SB and BB label-event expressions, including the
zero BB boundary at n = 6 for nonadjacent positions. -/
theorem two_label_marginals_nonnegative (n p : ℝ) (hn : 6 ≤ n)
    (hp : p = 0 ∨ p = 3 / n) :
    0 ≤ p / 6 ∧ 0 ≤ (3 / n - p) / (3 * (n - 3)) ∧
      0 ≤ (1 - 6 / n + p) / ((n - 3) * (n - 4)) := by
  have h0 : 0 < n := by linarith
  have h3 : 0 < n - 3 := by linarith
  have h4 : 0 < n - 4 := by linarith
  have hpn : 0 ≤ p ∧ p ≤ 3 / n := by
    rcases hp with rfl | rfl
    · exact ⟨le_rfl, div_nonneg (by norm_num) h0.le⟩
    · exact ⟨div_nonneg (by norm_num) h0.le, le_rfl⟩
  have h6 : 6 / n ≤ 1 := (div_le_one h0).2 hn
  refine ⟨div_nonneg hpn.1 (by norm_num),
    div_nonneg (sub_nonneg.mpr hpn.2) (by positivity), ?_⟩
  exact div_nonneg (by linarith [hpn.1]) (mul_pos h3 h4).le

/-- The strict endpoint is essential: at equality no contradiction follows. -/
theorem threshold_exceeds_fixed_factor (n beta : ℝ) (hn : 0 < n) :
    beta < (3 / 2 : ℝ) * (1 - 1 / n) ↔ 3 < (3 - 2 * beta) * n := by
  apply (mul_lt_mul_iff_left₀ (show 0 < 2 * n by positivity)).symm.trans
  field_simp
  constructor <;> intro h <;> nlinarith

variable {Tree Edge : Type*} [Fintype Edge]

def objective (c x : Edge → ℝ) : ℝ := ∑ e, c e * x e

/-- The finite nonnegative-maximization guarantee, expressed by a tree attaining
at least 1/beta of each relaxation value. It is indexed by the actual incidence
vectors, relaxation and factor; it is not a statement about unrelated totals. -/
structure MaxApproximation (incidence : Tree → Edge → ℝ)
    (R : Set (Edge → ℝ)) (beta : ℝ) : Prop where
  factor_ge_one : 1 ≤ beta
  contains : ∀ t, incidence t ∈ R
  bound : ∀ c, (∀ e, 0 ≤ c e) → ∀ x ∈ R,
    ∃ t, objective c x ≤ beta * objective c (incidence t)

theorem MaxApproximation.objective_le {incidence : Tree → Edge → ℝ}
    {R : Set (Edge → ℝ)} {beta : ℝ} (h : MaxApproximation incidence R beta)
    (c : Edge → ℝ) (hc : ∀ e, 0 ≤ c e) (opt : ℝ)
    (hopt : ∀ t, objective c (incidence t) ≤ opt)
    (x : Edge → ℝ) (hx : x ∈ R) : objective c x ≤ beta * opt := by
  obtain ⟨t, ht⟩ := h.bound c hc x hx
  exact ht.trans (mul_le_mul_of_nonneg_left (hopt t) (by linarith [h.factor_ge_one]))

def signedPoint [Fintype Tree] (w : Tree → ℝ) (incidence : Tree → Edge → ℝ) :
    Edge → ℝ := fun e => ∑ t, w t * incidence t e

theorem objective_signedPoint [Fintype Tree] (w : Tree → ℝ)
    (incidence : Tree → Edge → ℝ) (c : Edge → ℝ) :
    objective c (signedPoint w incidence) = ∑ t, w t * objective c (incidence t) := by
  unfold objective signedPoint
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Conditional geometric endpoint: the signed point's membership and its
triangle moment are explicit inputs. This is not the small-index/orbit theorem. -/
theorem factor_ge_threshold_of_signed_point [Fintype Tree]
    {incidence : Tree → Edge → ℝ} {R : Set (Edge → ℝ)} {beta : ℝ}
    (h : MaxApproximation incidence R beta) (n : ℝ) (hn : 0 < n)
    (w : Tree → ℝ) (c : Edge → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hopt : ∀ t, objective c (incidence t) ≤ 2)
    (hmember : signedPoint w incidence ∈ R)
    (hmoment : (∑ t, w t * objective c (incidence t)) = 3 * (n - 1) / n) :
    (3 / 2 : ℝ) * (1 - 1 / n) ≤ beta := by
  have hb := h.objective_le c hc 2 hopt (signedPoint w incidence) hmember
  rw [objective_signedPoint, hmoment] at hb
  have heq : 3 * (n - 1) / n = 2 * ((3 / 2 : ℝ) * (1 - 1 / n)) := by
    field_simp
  rw [heq] at hb
  linarith

/-- A strictly negative square moment for the signed path weights, once their
first and factorial second moments are known. -/
theorem negative_square_arithmetic (n : ℝ) (hn : 6 ≤ n) :
    4 - 3 * (3 * (n - 1) / n) + 12 / n = -5 + 21 / n ∧
      -5 + 21 / n < 0 := by
  have h0 : 0 < n := by linarith
  constructor
  · field_simp
    ring
  · have hh : 21 / n ≤ (7 / 2 : ℝ) := (div_le_iff₀ h0).2 (by nlinarith)
    linarith

/-- Boolean edge and bipartition indicators for the extracted research note. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

def cut (a b : Bool) : ℝ := if a = b then 0 else 1

/-- The triangle SOS identity for any proper two-coloring of the selected edges.
Application to all spanning trees still uses their bipartition property. -/
theorem triangle_sos_identity (z0 z1 z2 e01 e02 e12 : Bool)
    (h01 : e01 = true → z0 ≠ z1) (h02 : e02 = true → z0 ≠ z2)
    (h12 : e12 = true → z1 ≠ z2) :
    2 - (bit e01 + bit e02 + bit e12) =
      (1 / 2 : ℝ) * (2 - (cut z0 z1 + cut z0 z2 + cut z1 z2))^2 +
      (cut z0 z1 - bit e01)^2 + (cut z0 z2 - bit e02)^2 +
      (cut z1 z2 - bit e12)^2 := by
  cases z0 <;> cases z1 <;> cases z2 <;>
    cases e01 <;> cases e02 <;> cases e12 <;> norm_num [bit, cut] at *

end
end Lemmata.SpanningTreeSymmetricEF.Approximation
