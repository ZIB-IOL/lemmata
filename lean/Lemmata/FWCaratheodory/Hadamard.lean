module

public import Lemmata.FWCaratheodory.Objective
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# A lower bound for the approximate Carathéodory problem (Theorem 8.1)

Write `x = ∑_j λ_j c_j` for the normalized columns `c_j = H_j/n^{1/p}`, and `μ_j = λ_j - 1/n`, so
that `x - x⋆ = ∑_j μ_j c_j`. Orthogonality of the columns gives
`‖x - x⋆‖₂² = n^{1-2/p} ∑_j μ_j²`, the power mean inequality gives
`‖y‖₂² ≤ n^{1-2/p} ‖y‖_p²` for `p ≥ 2`, and `∑_j μ_j² = ∑_j λ_j² - 1/n ≥ 1/|S| - 1/n` by
Cauchy–Schwarz.
-/

namespace Lemmata.FWCaratheodory

open Lemmata.FrankWolfe Lemmata.FrankWolfeIntro.Proof

variable {n : ℕ} {p : ENNReal}

/-- The power mean inequality: `∑ y_i² ≤ n^{1 - 2/p} ‖y‖_p²` for `p ≥ 2`. -/
theorem sum_sq_le_norm_sq [Fact (1 ≤ p)] (hp2 : 2 ≤ p.toReal) (hn : 0 < n)
    (y : PiLp p (fun _ : Fin n => ℝ)) :
    ∑ i, y i ^ 2 ≤ (n : ℝ) ^ (1 - 2 / p.toReal) * ‖y‖ ^ 2 := by
  have hr : 0 < p.toReal := by linarith
  set P := p.toReal with hP
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lp_norm_sq hr]
  set A := ∑ i, (y i ^ 2) ^ (P / 2) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (sq_nonneg _) _
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ : Fin n => 1 / (n : ℝ))
    (fun i => y i ^ 2) (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    (fun i _ => sq_nonneg _) (show 1 ≤ P / 2 by linarith)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  set B := ∑ i, y i ^ 2 with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 := Real.rpow_le_rpow (by positivity) hJ (by positivity : (0 : ℝ) ≤ 2 / P)
  rw [← Real.rpow_mul (by positivity), show P / 2 * (2 / P) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow (by positivity) hA0] at h2
  have e : (1 / (n : ℝ)) ^ (2 / P) = (n : ℝ) ^ (-(2 / P)) := by
    rw [one_div, Real.inv_rpow hnr.le, Real.rpow_neg hnr.le]
  rw [e] at h2
  have e2 : (n : ℝ) ^ (1 - 2 / P) = (n : ℝ) * (n : ℝ) ^ (-(2 / P)) := by
    rw [sub_eq_add_neg, Real.rpow_add hnr, Real.rpow_one]
  rw [e2]
  have : B = (n : ℝ) * (1 / n * B) := by field_simp
  rw [this]
  calc (n : ℝ) * (1 / n * B) ≤ n * ((n : ℝ) ^ (-(2 / P)) * A ^ (2 / P)) :=
        mul_le_mul_of_nonneg_left h2 hnr.le
    _ = n * (n : ℝ) ^ (-(2 / P)) * A ^ (2 / P) := by ring

theorem hadamard_bound [Fact (1 ≤ p)] (hp2 : 2 ≤ p) (hpt : p ≠ ⊤)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j, H i j = 1 ∨ H i j = -1)
    (horth : ∀ j k, j ≠ k → ∑ i, H i j * H i k = 0) (ε : ℝ) (S : Finset (Fin n))
    (x : PiLp p (fun _ : Fin n => ℝ)) (hx : x ∈ convexHull ℝ (hadamardVertex p H '' ↑S))
    (hε : ‖x - hadamardCenter p H‖ ≤ ε) :
    1 ≤ (S.card : ℝ) * (ε ^ 2 + 1 / n) := by
  have hr2 : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp2
  have hr : 0 < p.toReal := by linarith
  set P := p.toReal with hP
  set col := hadamardVertex p H with hcol
  rw [← Finset.coe_image] at hx
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
  -- `S` is nonempty, so `n > 0`
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  obtain ⟨j0, -⟩ := hSne
  have hn : 0 < n := Fin.pos j0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c : ℝ := (n : ℝ) ^ (1 / P) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hnr _
  have hsq : ∀ i j, H i j ^ 2 = 1 := by
    intro i j; rcases hH i j with h | h <;> rw [h] <;> norm_num
  have hdiag : ∀ j, ∑ i, H i j * H i j = n := by
    intro j; simp only [← sq, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hcoord : ∀ j i, col j i = H i j / c := fun j i => rfl
  -- the columns are distinct
  have hinj : Set.InjOn col ↑S := by
    intro j _ k _ hjk
    by_contra hne
    have h1 := horth j k hne
    have h2 : ∀ i, H i j = H i k := by
      intro i
      have := congrArg (fun z : PiLp p (fun _ : Fin n => ℝ) => z i) hjk
      simp only [hcoord] at this
      field_simp at this
      exact this
    simp only [h2] at h1
    rw [hdiag k] at h1
    linarith
  rw [Finset.sum_image hinj] at hw1 hwx
  -- weights on all indices
  set lam : Fin n → ℝ := fun j => if j ∈ S then w (col j) else 0 with hlam
  have hlam0 : ∀ j ∉ S, lam j = 0 := fun j hj => by simp [hlam, hj]
  have hsumS : ∀ g : Fin n → ℝ, ∑ j ∈ S, w (col j) * g j = ∑ j, lam j * g j := by
    intro g
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hlam0 j hj, zero_mul])]
    apply Finset.sum_congr rfl; intro j hj; simp [hlam, hj]
  have hlam1 : ∑ j, lam j = 1 := by
    have := hsumS (fun _ => 1); simp only [mul_one] at this; rw [← this, hw1]
  -- coordinates of `x - x⋆`
  set μ : Fin n → ℝ := fun j => lam j - 1 / n with hμ
  have hxi : ∀ i, (x - hadamardCenter p H) i = ∑ j, μ j * H i j / c := by
    intro i
    have hx' : x i = ∑ j, lam j * (H i j / c) := by
      rw [← hwx, ← hsumS (fun j => H i j / c)]
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        hcoord]
    have hcen : hadamardCenter p H i = ∑ j, 1 / n * (H i j / c) := by
      simp only [hadamardCenter, WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply,
        Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      rfl
    rw [WithLp.ofLp_sub, Pi.sub_apply, hx', hcen, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp only [hμ]; ring
  -- `‖x - x⋆‖₂² = (n/c²) ∑ μ_j²`
  have hl2 : ∑ i, (x - hadamardCenter p H) i ^ 2 = n / c ^ 2 * ∑ j, μ j ^ 2 := by
    simp only [hxi]
    have e1 : ∀ i, (∑ j, μ j * H i j / c) ^ 2 =
        1 / c ^ 2 * ∑ j, ∑ k, μ j * μ k * (H i j * H i k) := by
      intro i
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      field_simp
    simp only [e1, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ j, ∑ i, ∑ k, μ j * μ k * (H i j * H i k) = n * μ j ^ 2 := by
      intro j
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single j]
      · rw [← Finset.mul_sum, hdiag j]; ring
      · intro k _ hkj
        rw [← Finset.mul_sum, horth j k (Ne.symm hkj), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    simp only [e2, ← Finset.mul_sum]
    ring
  -- the power mean inequality
  have hpm := sum_sq_le_norm_sq hr2 hn (x - hadamardCenter p H)
  rw [hl2] at hpm
  have hc2 : c ^ 2 = (n : ℝ) ^ (2 / P) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hnr.le]; congr 1; push_cast; ring
  have hfac : n / c ^ 2 = (n : ℝ) ^ (1 - 2 / P) := by
    rw [hc2, sub_eq_add_neg, Real.rpow_add hnr, Real.rpow_one, Real.rpow_neg hnr.le, div_eq_mul_inv]
  rw [hfac] at hpm
  have hpos : 0 < (n : ℝ) ^ (1 - 2 / P) := Real.rpow_pos_of_pos hnr _
  have hμle : ∑ j, μ j ^ 2 ≤ ‖x - hadamardCenter p H‖ ^ 2 := le_of_mul_le_mul_left hpm hpos
  have hnorm0 : 0 ≤ ‖x - hadamardCenter p H‖ := norm_nonneg _
  have hε2 : ‖x - hadamardCenter p H‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hnorm0 hε 2
  -- `∑ μ_j² = ∑ λ_j² - 1/n`
  have hμsum : ∑ j, μ j ^ 2 = ∑ j, lam j ^ 2 - 1 / n := by
    simp only [hμ, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, hlam1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  -- Cauchy–Schwarz
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := lam)
  have hS1 : ∑ j ∈ S, lam j = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hlam0 j hj), hlam1]
  have hS2 : ∑ j ∈ S, lam j ^ 2 = ∑ j, lam j ^ 2 :=
    Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hlam0 j hj]; ring)
  rw [hS1, hS2, one_pow] at hcs
  have hcard0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  calc (1 : ℝ) ≤ S.card * ∑ j, lam j ^ 2 := hcs
    _ = S.card * (∑ j, μ j ^ 2 + 1 / n) := by rw [hμsum]; ring
    _ ≤ S.card * (ε ^ 2 + 1 / n) := by
        apply mul_le_mul_of_nonneg_left _ hcard0
        linarith

namespace Proof

theorem hadamard_lower_bound : HadamardLowerBound := by
  intro n p _ hp2 hpt H hH horth ε S x hx hε
  exact hadamard_bound hp2 hpt H hH horth ε S x hx hε

end Proof

end Lemmata.FWCaratheodory
