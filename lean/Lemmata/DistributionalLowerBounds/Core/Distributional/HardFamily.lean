module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.Geometry
public import Mathlib.Tactic

@[expose] public section

/-!
# The Grimmer--Liu weighted hard set

This module formalizes the completion-of-squares representation used in
`tex/sc-lmo-distributional.tex`: the weighted Euclidean/ℓ₁ sublevel set is an
intersection of unit balls.  Consequently it is `1`-strongly convex in the
paper's ball-inclusion convention.

No algorithmic or probabilistic assumption occurs in this file.
-/

open Set

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- A Boolean encoding of the two signs. -/
def signVal : Bool → ℝ
  | false => -1
  | true => 1

@[simp] lemma signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by
  cases b <;> norm_num [signVal]

/-- Sign chosen to maximize `s*x`.  At zero we choose `+1`. -/
noncomputable def maximizingSign (x : ℝ) : Bool := decide (0 ≤ x)

@[simp] lemma signVal_maximizingSign_mul (x : ℝ) :
    signVal (maximizingSign x) * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [maximizingSign, hx, signVal, abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    simp [maximizingSign, hx, signVal, abs_of_neg hx']

/-- The signed weight vector associated with a cube vertex. -/
def signedWeight {d : ℕ} (w : Fin d → ℝ) (s : Fin d → Bool) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => w i * signVal (s i))

/-- Exact squared-norm expansion for a signed weight vector. -/
lemma norm_add_signedWeight_sq {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (w : Fin d → ℝ) (s : Fin d → Bool) :
    ‖x + signedWeight w s‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * ∑ i, w i * signVal (s i) * x i + ∑ i, w i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  change (∑ i, (x i + w i * signVal (s i)) ^ 2) =
    (∑ i, x i ^ 2) + 2 * ∑ i, w i * signVal (s i) * x i + ∑ i, w i ^ 2
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ i, 2 * x i * (w i * signVal (s i))) =
      2 * ∑ i, w i * signVal (s i) * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hw : (∑ i, (w i * signVal (s i)) ^ 2) = ∑ i, w i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, signVal_sq]
    ring
  rw [hcross, hw]

/-- Weighted quadratic/ℓ₁ sublevel-set formulation of the hard set. -/
def weightedHardSet {d : ℕ} (C : ℝ) (w : Fin d → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | (1 / 2 : ℝ) * ‖x‖ ^ 2 + ∑ i, w i * |x i| ≤ C ^ 2}

/-- Intersection-of-unit-balls formulation of the same set. -/
def hardBallIntersection {d : ℕ} (w : Fin d → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋂ s : Fin d → Bool, Metric.closedBall (-signedWeight w s) 1

private lemma signed_cross_le_abs {d : ℕ}
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : EuclideanSpace ℝ (Fin d)) (s : Fin d → Bool) :
    ∑ i, w i * signVal (s i) * x i ≤ ∑ i, w i * |x i| := by
  apply Finset.sum_le_sum
  intro i _
  have hs : signVal (s i) * x i ≤ |x i| := by
    cases s i <;> simp [signVal, neg_le_abs, le_abs_self]
  nlinarith [hw i]

/-- Completion of squares: if `∑wᵢ² + 2C² = 1`, the energy set is precisely
an intersection of unit balls centered at the signed weight vectors. -/
theorem weightedHardSet_eq_hardBallIntersection {d : ℕ}
    (C : ℝ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hnormalize : (∑ i, w i ^ 2) + 2 * C ^ 2 = 1) :
    weightedHardSet C w = hardBallIntersection w := by
  ext x
  constructor
  · intro hx
    change (1 / 2 : ℝ) * ‖x‖ ^ 2 + ∑ i, w i * |x i| ≤ C ^ 2 at hx
    rw [hardBallIntersection, Set.mem_iInter]
    intro s
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
    have hcross := signed_cross_le_abs w hw x s
    have hsquared : ‖x + signedWeight w s‖ ^ 2 ≤ 1 := by
      rw [norm_add_signedWeight_sq]
      nlinarith [hx, hcross, hnormalize]
    have hnorm0 : 0 ≤ ‖x + signedWeight w s‖ := norm_nonneg _
    nlinarith
  · intro hx
    rw [hardBallIntersection, Set.mem_iInter] at hx
    let s : Fin d → Bool := fun i => maximizingSign (x i)
    have hball := hx s
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hball
    have hsquared : ‖x + signedWeight w s‖ ^ 2 ≤ 1 := by
      have hnorm0 : 0 ≤ ‖x + signedWeight w s‖ := norm_nonneg _
      nlinarith
    change (1 / 2 : ℝ) * ‖x‖ ^ 2 + ∑ i, w i * |x i| ≤ C ^ 2
    rw [norm_add_signedWeight_sq] at hsquared
    have hsign : (∑ i, w i * signVal (s i) * x i) = ∑ i, w i * |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [s]
      calc
        w i * signVal (maximizingSign (x i)) * x i =
            w i * (signVal (maximizingSign (x i)) * x i) := by ring
        _ = w i * |x i| := by rw [signVal_maximizingSign_mul]
    rw [hsign] at hsquared
    nlinarith [hsquared, hnormalize]

/-- Normalization constant from the Grimmer--Liu family. -/
noncomputable def hardC (d : ℕ) : ℝ :=
  (Real.sqrt ((d : ℝ) ^ 2 + d + 2))⁻¹

/-- Increasing coordinate weights `C * sqrt(2(i+1))`, using zero-based `Fin`
indices. -/
noncomputable def hardWeight (d : ℕ) (i : Fin d) : ℝ :=
  hardC d * Real.sqrt (2 * (i.val + 1 : ℝ))

lemma hardC_pos (d : ℕ) : 0 < hardC d := by
  dsimp [hardC]
  positivity

lemma hardC_sq (d : ℕ) :
    hardC d ^ 2 = 1 / ((d : ℝ) ^ 2 + d + 2) := by
  have hpos : 0 < (d : ℝ) ^ 2 + d + 2 := by positivity
  have hs : Real.sqrt ((d : ℝ) ^ 2 + d + 2) ^ 2 =
      ((d : ℝ) ^ 2 + d + 2) := Real.sq_sqrt hpos.le
  dsimp [hardC]
  rw [inv_pow, hs]
  field_simp

lemma hardWeight_nonneg (d : ℕ) (i : Fin d) : 0 ≤ hardWeight d i := by
  dsimp [hardWeight, hardC]
  positivity

lemma hardWeight_sq (d : ℕ) (i : Fin d) :
    hardWeight d i ^ 2 = hardC d ^ 2 * 2 * (i.val + 1 : ℝ) := by
  have h : 0 ≤ 2 * (i.val + 1 : ℝ) := by positivity
  dsimp [hardWeight]
  rw [mul_pow, Real.sq_sqrt h]
  ring

lemma sum_fin_val_add_one (d : ℕ) :
    (∑ i : Fin d, ((i.val : ℝ) + 1)) = (d : ℝ) * (d + 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

lemma sum_hardWeight_sq (d : ℕ) :
    (∑ i : Fin d, hardWeight d i ^ 2) =
      hardC d ^ 2 * (d : ℝ) * (d + 1) := by
  simp_rw [hardWeight_sq]
  rw [← Finset.mul_sum, sum_fin_val_add_one]
  ring

/-- The final (largest) weight `w_d`. -/
noncomputable def hardTopWeight (d : ℕ) : ℝ :=
  hardC d * Real.sqrt (2 * (d : ℝ))

lemma hardTopWeight_sq (d : ℕ) :
    hardTopWeight d ^ 2 = hardC d ^ 2 * 2 * d := by
  have h : 0 ≤ 2 * (d : ℝ) := by positivity
  dsimp [hardTopWeight]
  rw [mul_pow, Real.sq_sqrt h]
  ring

lemma hardWeight_le_top (d : ℕ) (i : Fin d) :
    hardWeight d i ≤ hardTopWeight d := by
  have hi : (i.val + 1 : ℝ) ≤ d := by exact_mod_cast i.isLt
  dsimp [hardWeight, hardTopWeight]
  apply mul_le_mul_of_nonneg_left _ (hardC_pos d).le
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma exists_hardWeight_lt_top {d : ℕ} (hd : 2 ≤ d) :
    ∃ i : Fin d, hardWeight d i < hardTopWeight d := by
  let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) hd⟩
  refine ⟨i, ?_⟩
  have harg : (2 : ℝ) * (i.val + 1) < 2 * d := by
    have h1d : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    simpa [i] using mul_lt_mul_of_pos_left h1d (show (0 : ℝ) < 2 by norm_num)
  dsimp [hardWeight, hardTopWeight]
  apply mul_lt_mul_of_pos_left _ (hardC_pos d)
  exact Real.sqrt_lt_sqrt (by positivity) harg

/-- The concrete constants satisfy the unit-ball normalization exactly. -/
lemma hardWeight_normalization (d : ℕ) :
    (∑ i : Fin d, hardWeight d i ^ 2) + 2 * hardC d ^ 2 = 1 := by
  rw [sum_hardWeight_sq, hardC_sq]
  have hden : (d : ℝ) ^ 2 + d + 2 ≠ 0 := by positivity
  field_simp

/-- The normalized weighted hard set is `1`-strongly convex. -/
theorem weightedHardSet_isStronglyConvexBall {d : ℕ}
    (C : ℝ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hnormalize : (∑ i, w i ^ 2) + 2 * C ^ 2 = 1) :
    IsStronglyConvexBall (weightedHardSet C w) 1 := by
  rw [weightedHardSet_eq_hardBallIntersection C w hw hnormalize]
  rw [show hardBallIntersection w =
      ⋂₀ Set.range (fun s : Fin d → Bool =>
        Metric.closedBall (-signedWeight w s) 1) by
    simp [hardBallIntersection]]
  apply isStronglyConvexBall_sInter (by norm_num)
  intro B hB
  rcases hB with ⟨s, rfl⟩
  exact isStronglyConvexBall_closedBall_one _

/-- Coordinate weights after hiding their order by a permutation. -/
noncomputable def permutedHardWeight
    (d : ℕ) (π : Equiv.Perm (Fin d)) (i : Fin d) : ℝ :=
  hardWeight d (π i)

lemma permutedHardWeight_normalization (d : ℕ) (π : Equiv.Perm (Fin d)) :
    (∑ i : Fin d, permutedHardWeight d π i ^ 2) + 2 * hardC d ^ 2 = 1 := by
  rw [show (∑ i : Fin d, permutedHardWeight d π i ^ 2) =
      ∑ i : Fin d, hardWeight d i ^ 2 by
    exact Equiv.sum_comp π (fun i => hardWeight d i ^ 2)]
  exact hardWeight_normalization d

/-- Paper-facing endpoint: every permuted Grimmer--Liu set is `1`-strongly
convex. -/
theorem concreteHardSet_isStronglyConvexBall
    (d : ℕ) (π : Equiv.Perm (Fin d)) :
    IsStronglyConvexBall
      (weightedHardSet (hardC d) (permutedHardWeight d π)) 1 :=
  weightedHardSet_isStronglyConvexBall (hardC d) (permutedHardWeight d π)
    (fun i => hardWeight_nonneg d (π i)) (permutedHardWeight_normalization d π)

end Lemmata.DistributionalLowerBounds.Core.Distributional
