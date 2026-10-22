module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.ExactLMO
public import Lemmata.DistributionalLowerBounds.Core.Distributional.Diameter
public import Mathlib.Tactic

@[expose] public section

/-!
# Optimizer and quadratic-gap identities

These endpoints cover the deterministic analytic/algebraic steps around
`eq:rho`, `eq:objective`, `eq:optimum`, and `cor:conditional-error` in the
paper.  They do not formalize the posterior probability law.
-/

open InnerProductSpace
local notation "inner" => inner ℝ

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Coordinate proposed by the hard-instance optimizer. -/
def optimizerCoordinate (rho wd w : ℝ) : ℝ := rho * (wd - w)

/-- Objective center and KKT multiplier. -/
noncomputable def optimizerMultiplier (rho : ℝ) : ℝ := rho / (1 - rho)
noncomputable def objectiveCenter (rho wd : ℝ) : ℝ := optimizerMultiplier rho * wd

/-- The coordinatewise KKT stationarity identity.  The only denominator
condition needed is `rho ≠ 1`. -/
lemma optimizer_stationarity {rho wd w : ℝ} (hrho : rho ≠ 1) :
    optimizerCoordinate rho wd w - objectiveCenter rho wd +
      optimizerMultiplier rho * (optimizerCoordinate rho wd w + w) = 0 := by
  simp only [optimizerCoordinate, objectiveCenter, optimizerMultiplier]
  have hden : 1 - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho)
  field_simp [hden]
  ring

/-- Substitution of the proposed optimizer into one weighted constraint term. -/
lemma optimizer_constraint_coordinate (rho wd w : ℝ) :
    (1 / 2 : ℝ) * optimizerCoordinate rho wd w ^ 2 +
      w * optimizerCoordinate rho wd w =
    (1 / 2 : ℝ) * rho ^ 2 * (wd - w) ^ 2 + rho * w * (wd - w) := by
  simp [optimizerCoordinate]
  ring

/-- The scalar function defining `rho`. -/
noncomputable def rhoLHS {d : ℕ} (w : Fin d → ℝ) (wd rho : ℝ) : ℝ :=
  ∑ i, ((1 / 2 : ℝ) * rho ^ 2 * (wd - w i) ^ 2 +
    rho * w i * (wd - w i))

/-- `rhoLHS` vanishes at zero. -/
@[simp] lemma rhoLHS_zero {d : ℕ} (w : Fin d → ℝ) (wd : ℝ) :
    rhoLHS w wd 0 = 0 := by simp [rhoLHS]

/-- Each coordinate contribution is strictly increasing on nonnegative `rho`
when its weight lies in `[0,wd]` and at least one gap is positive. -/
lemma rhoLHS_strictMonoOn {d : ℕ} (w : Fin d → ℝ) (wd : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwd : ∀ i, w i ≤ wd)
    (hgap : ∃ i, w i < wd) :
    StrictMonoOn (rhoLHS w wd) (Set.Ici 0) := by
  intro a ha b hb hab
  rcases hgap with ⟨j, hj⟩
  have hgapj : 0 < wd - w j := sub_pos.mpr hj
  have ha0 : 0 ≤ a := ha
  have hbpos : 0 < b := lt_of_le_of_lt ha0 hab
  have hba_pos : 0 < b + a := add_pos_of_pos_of_nonneg hbpos ha0
  have hdiff_pos : 0 < b - a := sub_pos.mpr hab
  have hsq_pos : 0 < b ^ 2 - a ^ 2 := by
    nlinarith [mul_pos hdiff_pos hba_pos]
  have hterm_nonneg : ∀ i,
      0 ≤ ((1 / 2 : ℝ) * (b ^ 2 - a ^ 2) * (wd - w i) ^ 2 +
        (b - a) * w i * (wd - w i)) := by
    intro i
    have hwi : 0 ≤ wd - w i := sub_nonneg.mpr (hwd i)
    have hfirst : 0 ≤ (1 / 2 : ℝ) * (b ^ 2 - a ^ 2) * (wd - w i) ^ 2 := by
      positivity
    have hsecond : 0 ≤ (b - a) * w i * (wd - w i) :=
      mul_nonneg (mul_nonneg hdiff_pos.le (hw0 i)) hwi
    linarith
  have hterm_pos :
      0 < ((1 / 2 : ℝ) * (b ^ 2 - a ^ 2) * (wd - w j) ^ 2 +
        (b - a) * w j * (wd - w j)) := by
    have hfirst : 0 < (1 / 2 : ℝ) * (b ^ 2 - a ^ 2) * (wd - w j) ^ 2 := by
      positivity
    have hsecond : 0 ≤ (b - a) * w j * (wd - w j) :=
      mul_nonneg (mul_nonneg hdiff_pos.le (hw0 j)) hgapj.le
    linarith
  have hsum_pos : 0 < ∑ i,
      ((1 / 2 : ℝ) * (b ^ 2 - a ^ 2) * (wd - w i) ^ 2 +
        (b - a) * w i * (wd - w i)) := by
    exact Finset.sum_pos' (fun i _ => hterm_nonneg i)
      ⟨j, Finset.mem_univ j, hterm_pos⟩
  dsimp [rhoLHS]
  rw [← sub_pos]
  convert hsum_pos using 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Existence and uniqueness of the paper's `rho` from the endpoint
inequality.  This packages the continuity argument independently of the
particular square-root weights. -/
theorem existsUnique_rho {d : ℕ} (w : Fin d → ℝ) (wd C : ℝ)
    (hC : 0 < C)
    (hw0 : ∀ i, 0 ≤ w i) (hwd : ∀ i, w i ≤ wd)
    (hgap : ∃ i, w i < wd)
    (hone : C ^ 2 < rhoLHS w wd 1) :
    ∃! rho : ℝ, rho ∈ Set.Ioo (0 : ℝ) 1 ∧ rhoLHS w wd rho = C ^ 2 := by
  have hmono := rhoLHS_strictMonoOn w wd hw0 hwd hgap
  have hcont : Continuous (rhoLHS w wd) := by
    unfold rhoLHS
    fun_prop
  have htarget : C ^ 2 ∈ Set.Icc (rhoLHS w wd 0) (rhoLHS w wd 1) := by
    rw [rhoLHS_zero]
    exact ⟨sq_nonneg C, hone.le⟩
  rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      hcont.continuousOn htarget) with ⟨rho, hrhoIcc, hrhoEq⟩
  have hrho0 : 0 < rho := by
    by_contra h
    have : rho = 0 := le_antisymm (le_of_not_gt h) hrhoIcc.1
    subst rho
    simp at hrhoEq
    nlinarith [sq_pos_of_pos hC]
  have hrho1 : rho < 1 := by
    by_contra h
    have : rho = 1 := le_antisymm hrhoIcc.2 (le_of_not_gt h)
    subst rho
    linarith
  refine ⟨rho, ⟨⟨hrho0, hrho1⟩, hrhoEq⟩, ?_⟩
  intro r hr
  exact hmono.injOn hr.1.1.le hrhoIcc.1 ((hr.2).trans hrhoEq.symm)

/-- At `rho=1`, the defining expression telescopes to half the sum of squared
weight gaps. -/
lemma rhoLHS_one {d : ℕ} (w : Fin d → ℝ) (wd : ℝ) :
    rhoLHS w wd 1 = (1 / 2 : ℝ) * ∑ i, (wd ^ 2 - w i ^ 2) := by
  simp only [rhoLHS, one_pow, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Sum identity behind the endpoint computation for the concrete weights. -/
lemma sum_top_sq_sub_hardWeight (d : ℕ) :
    (∑ i : Fin d, (hardTopWeight d ^ 2 - hardWeight d i ^ 2)) =
      hardC d ^ 2 * d * (d - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_hardWeight_sq, hardTopWeight_sq]
  ring

/-- For `d≥3`, the concrete defining equation crosses `C²` before `rho=1`. -/
lemma concrete_rhoLHS_one_gt {d : ℕ} (hd : 3 ≤ d) :
    hardC d ^ 2 < rhoLHS (hardWeight d) (hardTopWeight d) 1 := by
  rw [rhoLHS_one, sum_top_sq_sub_hardWeight]
  have hC2 : 0 < hardC d ^ 2 := sq_pos_of_pos (hardC_pos d)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hprod : 0 ≤ ((d : ℝ) - 3) * ((d : ℝ) + 2) :=
    mul_nonneg (sub_nonneg.mpr hdR) (by positivity)
  have hfactor : (2 : ℝ) < (d : ℝ) * (d - 1) := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hfactor hC2
  nlinarith

/-- Paper-facing endpoint for existence and uniqueness of the scalar `rho` in
the concrete Grimmer--Liu construction. -/
theorem concrete_existsUnique_rho {d : ℕ} (hd : 3 ≤ d) :
    ∃! rho : ℝ,
      rho ∈ Set.Ioo (0 : ℝ) 1 ∧
        rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d ^ 2 := by
  apply existsUnique_rho (hardWeight d) (hardTopWeight d) (hardC d)
    (hardC_pos d) (hardWeight_nonneg d) (hardWeight_le_top d)
    (exists_hardWeight_lt_top (by omega)) (concrete_rhoLHS_one_gt hd)

/-- The concrete solution satisfies the lower bound `rho ≥ 2/d²` used in
the final complexity estimate. -/
theorem concrete_rho_lower_bound {d : ℕ} (hd : 3 ≤ d) {rho : ℝ}
    (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d ^ 2) :
    2 / (d : ℝ) ^ 2 ≤ rho := by
  have hterm : ∀ i : Fin d,
      (1 / 2 : ℝ) * rho ^ 2 * (hardTopWeight d - hardWeight d i) ^ 2 +
          rho * hardWeight d i * (hardTopWeight d - hardWeight d i) ≤
        (rho / 2) * (hardTopWeight d ^ 2 - hardWeight d i ^ 2) := by
    intro i
    have hgap : 0 ≤ hardTopWeight d - hardWeight d i :=
      sub_nonneg.mpr (hardWeight_le_top d i)
    have hri : 0 ≤ 1 - rho := sub_nonneg.mpr hrho.2.le
    have hr0 : 0 ≤ rho := hrho.1.le
    nlinarith [mul_nonneg hri (sq_nonneg (hardTopWeight d - hardWeight d i))]
  have hsum : rhoLHS (hardWeight d) (hardTopWeight d) rho ≤
      (rho / 2) * ∑ i : Fin d,
        (hardTopWeight d ^ 2 - hardWeight d i ^ 2) := by
    rw [rhoLHS, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  rw [heq, sum_top_sq_sub_hardWeight] at hsum
  have hC2 : 0 < hardC d ^ 2 := sq_pos_of_pos (hardC_pos d)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hfactored :
      hardC d ^ 2 * 1 ≤
        hardC d ^ 2 * (rho * (d : ℝ) * ((d : ℝ) - 1) / 2) := by
    convert hsum using 1 <;> ring
  have hone : (1 : ℝ) ≤ rho * (d : ℝ) * ((d : ℝ) - 1) / 2 :=
    le_of_mul_le_mul_left hfactored hC2
  have hmain : (2 : ℝ) ≤ rho * (d : ℝ) * ((d : ℝ) - 1) := by
    nlinarith
  have hdd : (d : ℝ) * ((d : ℝ) - 1) ≤ d ^ 2 := by nlinarith
  have hr0 : 0 ≤ rho := hrho.1.le
  have hmain' : (2 : ℝ) ≤ rho * d ^ 2 :=
    hmain.trans (by nlinarith)
  exact (div_le_iff₀ (sq_pos_of_pos hdpos)).2 (by nlinarith)

/-- Vector of proposed optimizer coordinates. -/
def optimizerPoint {d : ℕ} (rho wd : ℝ) (w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => optimizerCoordinate rho wd (w i)

/-- Coordinate-sum quadratic objective centered at the constant vector `M`. -/
noncomputable def coordinateObjective {d : ℕ} (M : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (1 / 2 : ℝ) * (x i - M) ^ 2

/-- Strong subgradient inequality for one weighted-energy coordinate at a
nonnegative base point. -/
lemma nonnegative_energy_strong_subgradient
    {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) (y : ℝ) :
    (1 / 2 : ℝ) * z ^ 2 + w * |z| +
        (z + w) * (y - z) + (1 / 2 : ℝ) * (y - z) ^ 2 ≤
      (1 / 2 : ℝ) * y ^ 2 + w * |y| := by
  rw [abs_of_nonneg hz]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    ring_nf
    exact le_rfl
  · have hy' : y < 0 := lt_of_not_ge hy
    rw [abs_of_neg hy']
    nlinarith [mul_nonneg hw (le_of_lt (neg_pos.mpr hy'))]

/-- Boundary equation for the proposed optimizer. -/
lemma optimizerPoint_boundary {d : ℕ} (w : Fin d → ℝ) (wd rho C : ℝ)
    (hrho : 0 ≤ rho) (hwd : ∀ i, w i ≤ wd)
    (heq : rhoLHS w wd rho = C ^ 2) :
    coordinateEnergy w (optimizerPoint rho wd w) = C ^ 2 := by
  rw [coordinateEnergy]
  calc
    (∑ i, ((1 / 2 : ℝ) * optimizerPoint rho wd w i ^ 2 +
        w i * |optimizerPoint rho wd w i|)) =
        ∑ i, ((1 / 2 : ℝ) * optimizerPoint rho wd w i ^ 2 +
          w i * optimizerPoint rho wd w i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_of_nonneg]
            exact mul_nonneg hrho (sub_nonneg.mpr (hwd i))
    _ = rhoLHS w wd rho := by
      apply Finset.sum_congr rfl
      intro i _
      exact optimizer_constraint_coordinate rho wd (w i)
    _ = C ^ 2 := heq

/-- The proposed point uniquely minimizes the quadratic objective over the
weighted hard set.  This is a direct strong-convexity/subgradient proof of the
paper's optimizer formula. -/
theorem optimizerPoint_unique_minimizer {d : ℕ}
    (w : Fin d → ℝ) (wd C rho : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwd : ∀ i, w i ≤ wd)
    (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS w wd rho = C ^ 2) :
    let xstar := optimizerPoint rho wd w
    let M := objectiveCenter rho wd
    coordinateEnergy w xstar = C ^ 2 ∧
      ∀ y : Fin d → ℝ, coordinateEnergy w y ≤ C ^ 2 →
        coordinateObjective M xstar ≤ coordinateObjective M y ∧
          (coordinateObjective M y = coordinateObjective M xstar → y = xstar) := by
  let xstar := optimizerPoint rho wd w
  let M := objectiveCenter rho wd
  have hboundary : coordinateEnergy w xstar = C ^ 2 :=
    optimizerPoint_boundary w wd rho C hrho.1.le hwd heq
  refine ⟨hboundary, ?_⟩
  intro y hy
  have hstrong : coordinateEnergy w xstar +
      ∑ i, (xstar i + w i) * (y i - xstar i) +
      (1 / 2 : ℝ) * ∑ i, (y i - xstar i) ^ 2 ≤ coordinateEnergy w y := by
    unfold coordinateEnergy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ =>
      nonnegative_energy_strong_subgradient
        (mul_nonneg hrho.1.le (sub_nonneg.mpr (hwd i))) (hw i) (y i))
  have hnormal : ∑ i, (xstar i + w i) * (y i - xstar i) ≤ 0 := by
    rw [hboundary] at hstrong
    have hsumsq : 0 ≤ ∑ i, (y i - xstar i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have hstationary : ∀ i,
      xstar i - M = -optimizerMultiplier rho * (xstar i + w i) := by
    intro i
    have hs := optimizer_stationarity (wd := wd) (w := w i) (ne_of_lt hrho.2)
    dsimp [xstar, M, optimizerPoint] at hs ⊢
    linarith
  have hgap : coordinateObjective M y - coordinateObjective M xstar =
      (1 / 2 : ℝ) * ∑ i, (y i - xstar i) ^ 2 -
        optimizerMultiplier rho *
          ∑ i, (xstar i + w i) * (y i - xstar i) := by
    unfold coordinateObjective
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i, ((1 / 2 : ℝ) * (y i - M) ^ 2 -
          (1 / 2 : ℝ) * (xstar i - M) ^ 2)) =
          ∑ i, ((1 / 2 : ℝ) * (y i - xstar i) ^ 2 -
            optimizerMultiplier rho * (xstar i + w i) * (y i - xstar i)) := by
              apply Finset.sum_congr rfl
              intro i _
              have hyM : y i - M =
                  (y i - xstar i) -
                    optimizerMultiplier rho * (xstar i + w i) := by
                linarith [hstationary i]
              rw [hyM, hstationary i]
              ring
      _ = (1 / 2 : ℝ) * ∑ i, (y i - xstar i) ^ 2 -
          optimizerMultiplier rho *
            ∑ i, (xstar i + w i) * (y i - xstar i) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
              apply congrArg₂ (· - ·) rfl
              apply Finset.sum_congr rfl
              intro i _
              ring
  have hgamma : 0 < optimizerMultiplier rho := by
    dsimp [optimizerMultiplier]
    exact div_pos hrho.1 (sub_pos.mpr hrho.2)
  have hgap_nonneg : 0 ≤ coordinateObjective M y - coordinateObjective M xstar := by
    rw [hgap]
    have hsumsq : 0 ≤ ∑ i, (y i - xstar i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hprod : 0 ≤ -optimizerMultiplier rho *
        ∑ i, (xstar i + w i) * (y i - xstar i) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hgamma.le) hnormal
    nlinarith
  refine ⟨by linarith, ?_⟩
  intro hequal
  have hsumsq_le : ∑ i, (y i - xstar i) ^ 2 ≤ 0 := by
    have hprodlower : 0 ≤ -optimizerMultiplier rho *
        ∑ i, (xstar i + w i) * (y i - xstar i) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hgamma.le) hnormal
    have hgapzero : coordinateObjective M y - coordinateObjective M xstar = 0 := by
      linarith
    rw [hgap] at hgapzero
    nlinarith
  have hsumsq0 : ∑ i, (y i - xstar i) ^ 2 = 0 :=
    le_antisymm hsumsq_le (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hiff := Finset.sum_eq_zero_iff_of_nonneg
    (s := (Finset.univ : Finset (Fin d))) (f := fun i => (y i - xstar i) ^ 2)
    (fun i _ => sq_nonneg _)
  funext i
  have hi := (hiff.mp hsumsq0) i (Finset.mem_univ i)
  nlinarith

/-- Permuting coordinate weights does not change the scalar `rho` equation. -/
lemma rhoLHS_permutedHardWeight (d : ℕ) (π : Equiv.Perm (Fin d)) (rho : ℝ) :
    rhoLHS (permutedHardWeight d π) (hardTopWeight d) rho =
      rhoLHS (hardWeight d) (hardTopWeight d) rho := by
  unfold rhoLHS permutedHardWeight
  exact Equiv.sum_comp π (fun i =>
    (1 / 2 : ℝ) * rho ^ 2 * (hardTopWeight d - hardWeight d i) ^ 2 +
      rho * hardWeight d i * (hardTopWeight d - hardWeight d i))

/-- Paper-facing optimizer endpoint for every hidden permutation. -/
theorem concrete_optimizerPoint_unique_minimizer
    {d : ℕ} (π : Equiv.Perm (Fin d)) {rho : ℝ}
    (hrho : rho ∈ Set.Ioo (0 : ℝ) 1)
    (heq : rhoLHS (hardWeight d) (hardTopWeight d) rho = hardC d ^ 2) :
    let xstar := optimizerPoint rho (hardTopWeight d) (permutedHardWeight d π)
    let M := objectiveCenter rho (hardTopWeight d)
    coordinateEnergy (permutedHardWeight d π) xstar = hardC d ^ 2 ∧
      ∀ y : Fin d → ℝ,
        coordinateEnergy (permutedHardWeight d π) y ≤ hardC d ^ 2 →
        coordinateObjective M xstar ≤ coordinateObjective M y ∧
          (coordinateObjective M y = coordinateObjective M xstar → y = xstar) := by
  apply optimizerPoint_unique_minimizer
    (permutedHardWeight d π) (hardTopWeight d) (hardC d) rho
    (fun i => hardWeight_nonneg d (π i))
    (fun i => hardWeight_le_top d (π i)) hrho
  rw [rhoLHS_permutedHardWeight]
  exact heq

/-- Exact quadratic gap decomposition in a real inner-product space. -/
lemma quadratic_gap_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x xstar center : E) :
    (1 / 2 : ℝ) * ‖x - center‖ ^ 2 - (1 / 2 : ℝ) * ‖xstar - center‖ ^ 2 =
      (1 / 2 : ℝ) * ‖x - xstar‖ ^ 2 +
        inner (xstar - center) (x - xstar) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm]
  rw [real_inner_self_eq_norm_sq]
  ring

/-- Constrained first-order optimality converts the quadratic objective gap to
half the squared distance. -/
lemma quadratic_gap_ge_half_sqDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x xstar center : E}
    (hfirst : 0 ≤ inner (xstar - center) (x - xstar)) :
    (1 / 2 : ℝ) * ‖x - center‖ ^ 2 - (1 / 2 : ℝ) * ‖xstar - center‖ ^ 2 ≥
      (1 / 2 : ℝ) * ‖x - xstar‖ ^ 2 := by
  rw [quadratic_gap_identity]
  linarith

end Lemmata.DistributionalLowerBounds.Core.Distributional
