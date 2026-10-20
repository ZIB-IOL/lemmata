module

public import Lemmata.LPHardnessInP.ParityExtension.Separation
public import Lemmata.LPHardnessInP.Parity.Main
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

namespace Lemmata.LPHardnessInP.ParityExtension

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit
open Lemmata.LPHardnessInP.Parity

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A probability distribution on a finite matrix, represented by its
nonnegative masses. No measure-theoretic existence assumption is needed. -/
structure ProbabilityMatrix (I J : Type*) [Fintype I] [Fintype J] where
  mass : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  total : ∑ i, ∑ j, mass i j = 1

/-- A distribution is supported where the violation count has value `a`. -/
def SupportedAt (μ : ProbabilityMatrix I J) (t : I → J → ℝ) (a : ℝ) : Prop :=
  ∀ i j, μ.mass i j ≠ 0 → t i j = a

/-- The mass of a rectangle. -/
def rectangleMass (μ : ProbabilityMatrix I J) (R : Finset I) (C : Finset J) : ℝ :=
  ∑ i ∈ R, ∑ j ∈ C, μ.mass i j

/-- The finite corruption inequality, before conversion into a rank bound. -/
def CorruptionBound (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (A B E : ℝ) : Prop :=
  ∀ R C, rectangleMass μ₃ R C ≤
    A * rectangleMass μₕ R C + B * rectangleMass μ₁ R C + E

/-- The signed matrix separating the shifted violation matrix. -/
def signedWitness (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (A B : ℝ) : I → J → ℝ :=
  fun i j => μ₃.mass i j - A * μₕ.mass i j - B * μ₁.mass i j

theorem supported_pairing (μ : ProbabilityMatrix I J) (t : I → J → ℝ)
    {a : ℝ} (hs : SupportedAt μ t a) (r : ℝ) :
    pairing μ.mass (fun i j => t i j - r) = a - r := by
  have hterm : ∀ i j, μ.mass i j * (t i j - r) = μ.mass i j * (a - r) := by
    intro i j
    by_cases hz : μ.mass i j = 0
    · simp [hz]
    · rw [hs i j hz]
  simp only [pairing, hterm, ← Finset.sum_mul, μ.total, one_mul]

theorem signedWitness_rectangle_bound
    (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (A B E : ℝ)
    (h : CorruptionBound μ₃ μₕ μ₁ A B E) :
    RectangleBound (signedWitness μ₃ μₕ μ₁ A B) E := by
  intro R C
  have hb := h R C
  simp only [signedWitness, Finset.sum_sub_distrib, ← Finset.mul_sum]
  dsimp [rectangleMass] at hb
  linarith

theorem signedWitness_pairing
    (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (t : I → J → ℝ)
    {h : ℝ} (h₃ : SupportedAt μ₃ t 3) (hₕ : SupportedAt μₕ t h)
    (h₁ : SupportedAt μ₁ t 1) (A B r : ℝ) :
    pairing (signedWitness μ₃ μₕ μ₁ A B) (fun i j => t i j - r) =
      (3 - r) - A * (h - r) - B * (1 - r) := by
  have hlinear :
      pairing (signedWitness μ₃ μₕ μ₁ A B) (fun i j => t i j - r) =
        pairing μ₃.mass (fun i j => t i j - r) -
          A * pairing μₕ.mass (fun i j => t i j - r) -
          B * pairing μ₁.mass (fun i j => t i j - r) := by
    simp only [pairing, signedWitness, sub_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlinear, supported_pairing μ₃ t h₃ r, supported_pairing μₕ t hₕ r,
    supported_pairing μ₁ t h₁ r]

/-- Exact gap identity; the coefficient tending to three is what permits
every fixed positive subtraction. -/
theorem witness_gap_identity (A B h r : ℝ) :
    (3 - r) - A * (h - r) - B * (1 - r) =
      2 * r - A * (h - r) - (B - 3) * (1 - r) := by ring

/-- A useful quantitative form, with explicit error budgets. -/
theorem witness_gap_positive {A B h r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hA : 0 ≤ A) (hAh : A * h ≤ r / 4) (hB : B - 3 ≤ r / 4) :
    3 * r / 2 ≤ (3 - r) - A * (h - r) - B * (1 - r) := by
  rw [witness_gap_identity]
  have hAr : 0 ≤ A * r := mul_nonneg hA hr.le
  have hBr := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hr1)
  nlinarith [sq_nonneg r]

-- DOCS_BEGIN_MAIN
/-- The finite rank consequence of the three-distribution corruption bound.
The source rank lower bound is a conclusion, rather than an assumption. -/
theorem shifted_rank_lower_bound
    (μ₃ μₕ μ₁ : ProbabilityMatrix I J) (t : I → J → ℝ)
    {h A B E U r : ℝ} {L : ℕ}
    (h₃ : SupportedAt μ₃ t 3) (hₕ : SupportedAt μₕ t h)
    (h₁ : SupportedAt μ₁ t 1)
    (hcorr : CorruptionBound μ₃ μₕ μ₁ A B E)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hupper : ∀ i j, t i j - r ≤ U)
    (hgap : ((L : ℝ) - 1) * E * U <
      (3 - r) - A * (h - r) - B * (1 - r)) :
    (L : ℕ∞) ≤ nonnegativeRank (fun i j => t i j - r) := by
  apply rank_lower_bound_of_rectangle_bound hupper hE hU
    (signedWitness_rectangle_bound μ₃ μₕ μ₁ A B E hcorr)
  rwa [signedWitness_pairing μ₃ μₕ μ₁ t h₃ hₕ h₁ A B r]
-- DOCS_END_MAIN

noncomputable instance (n : ℕ) : Fintype (ParityLabel n) :=
  Fintype.ofInjective (fun L : ParityLabel n => (L.left, L.right)) (by
    intro a b h
    cases a
    cases b
    simp_all)

noncomputable instance (n : ℕ) : Fintype (ParityMatching n) :=
  Fintype.ofInjective (fun M : ParityMatching n => (M.perm, M.red)) (by
    intro a b h
    cases a
    cases b
    simp_all)

theorem violationCount_le_order {n : ℕ} (L : ParityLabel n) (M : ParityMatching n) :
    violationCount L M ≤ n := by
  unfold violationCount
  calc
    (∑ i : Fin n, if Violates L i (M.perm i) (M.red i) then 1 else 0) ≤
        ∑ _i : Fin n, 1 := Finset.sum_le_sum (by intro i _; split_ifs <;> omega)
    _ = n := by simp

/-- Application of the new finite rank argument to the concrete parity
matching LP. The hypotheses are distributions, their support, and a
rectangle estimate, rather than a nonnegative-rank lower bound. -/
theorem parity_lp_lower_bound_from_corruption
    {n m L : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (hn : 0 < n) (α : ℝ) (hα : 1 < α)
    (C : Lemmata.LPHardnessInP.Formulation.CertifiedLP (V := V)
      (fun (a : ParityLabel n) M => matchingCost a (2 * (α - 1) * n) M)
      (fun _ => ((n : ℝ) + 2 * (α - 1) * n) / α) m)
    (μ₃ μₕ μ₁ : ProbabilityMatrix (ParityLabel n) (ParityMatching n))
    {h A B E : ℝ}
    (h₃ : SupportedAt μ₃ (fun a M => (violationCount a M : ℝ)) 3)
    (hₕ : SupportedAt μₕ (fun a M => (violationCount a M : ℝ)) h)
    (h₁ : SupportedAt μ₁ (fun a M => (violationCount a M : ℝ)) 1)
    (hcorr : CorruptionBound μ₃ μₕ μ₁ A B E) (hE : 0 ≤ E)
    (hgap : ((L : ℝ) - 1) * E * n <
      (3 - 1 / (2 * α)) - A * (h - 1 / (2 * α)) - B * (1 - 1 / (2 * α))) :
    L ≤ m + 1 := by
  apply parity_matching_lp_lower_bound hn α hα C
  apply shifted_rank_lower_bound μ₃ μₕ μ₁ _ h₃ hₕ h₁ hcorr hE
    (Nat.cast_nonneg n) ?_ hgap
  intro a M
  have ht : (violationCount a M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast violationCount_le_order a M
  have hr : 0 ≤ 1 / (2 * α) := by positivity
  linarith

end Lemmata.LPHardnessInP.ParityExtension
