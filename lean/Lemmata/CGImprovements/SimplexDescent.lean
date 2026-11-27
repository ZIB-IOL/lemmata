module

public import Lemmata.CGImprovements.Statement
public import Lemmata.FrankWolfe.Proof.Calculus

@[expose] public section

/-!
# The simplex descent step (Lemma 3.45)

Along the projected gradient `d` the derivative is `⟨∇h(λ), d⟩ = ‖d‖²`, so smoothness gives
`h(λ - s d) ≤ h(λ) - s ‖d‖² + (L/2) s² ‖d‖²`. If `γ L ≤ 1` the endpoint does not increase `h`;
otherwise `λ - d/L` lies on the segment and `h` drops by `‖d‖²/(2L)`, while
`‖d‖² ≥ d_i² + d_j² ≥ (d_i - d_j)²/2`.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

namespace Proof

theorem simplex_descent : SimplexDescent := by
  intro k h L lam d lam' γ hsm hγ hd hlam' hmin
  set g := fderiv ℝ h lam with hg
  obtain ⟨G, hG⟩ : ∃ G : Fin k → ℝ, ∀ i, G i = g (EuclideanSpace.single i 1) := ⟨_, fun i => rfl⟩
  simp only [← hG] at hd ⊢
  have hgy : ∀ y : EuclideanSpace ℝ (Fin k), g y = ∑ i, y i * G i := fun y => by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr y]
    simp [hG, map_sum, map_smul, EuclideanSpace.basisFun_apply]
  have hnorm : ‖d‖ ^ 2 = ∑ i, d i ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; simp
  have hgd : g d = ‖d‖ ^ 2 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [hgy, hnorm]
    · have hsum : ∑ i, d i = 0 := by
        simp only [hd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring
      have e : ∀ i, d i * G i = d i ^ 2 + d i * ((∑ j, G j) / k) := fun i => by rw [hd i]; ring
      rw [hgy, hnorm]
      simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, add_zero]
  have hquad : ∀ s : ℝ, h (lam - s • d) ≤ h lam - s * ‖d‖ ^ 2 + L / 2 * s ^ 2 * ‖d‖ ^ 2 :=
    fun s => by
      have h1 := hsm.le_quadratic lam (lam - s • d)
      rw [show lam - s • d - lam = -(s • d) by abel, map_neg, map_smul, smul_eq_mul, norm_neg,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← hg, hgd] at h1
      linarith
  have hpair : ∀ i j, (G i - G j) ^ 2 ≤ 2 * ‖d‖ ^ 2 := fun i j => by
    have hij : G i - G j = d i - d j := by rw [hd i, hd j]; ring
    rw [hij, hnorm]
    by_cases hij' : i = j
    · subst hij'
      have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => sq_nonneg (d l))
      rw [sub_self]
      nlinarith
    · have h2 : d i ^ 2 + d j ^ 2 ≤ ∑ l, d l ^ 2 := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
          (fun l _ _ => sq_nonneg (d l))
        rwa [Finset.sum_pair hij'] at this
      nlinarith [sq_nonneg (d i + d j)]
  by_cases hγL : γ * L ≤ 1
  · left
    have h1 := hquad γ
    have h2 : (L : ℝ) / 2 * γ ^ 2 ≤ γ := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖d‖)
    linarith
  · right
    push Not at hγL
    have hL : (0 : ℝ) < L := by
      rcases eq_or_lt_of_le L.coe_nonneg with hL0 | hL0
      · rw [← hL0, mul_zero] at hγL; linarith
      · exact hL0
    have hγL0 : (0 : ℝ) < γ * L := by linarith
    have hs : lam - (1 / (L : ℝ)) • d ∈ segment ℝ lam (lam - γ • d) := by
      refine ⟨1 - 1 / (γ * L), 1 / (γ * L), ?_, (one_div_pos.mpr hγL0).le, by ring, ?_⟩
      · rw [sub_nonneg, div_le_one hγL0]; exact hγL.le
      · have e : 1 / (γ * L) * γ = 1 / (L : ℝ) := by
          rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff hγL0.ne' hL.ne']; ring
        rw [← e]
        module
    have h1 := hmin _ hs
    have h2 := hquad (1 / L)
    have e : h lam - 1 / L * ‖d‖ ^ 2 + L / 2 * (1 / L) ^ 2 * ‖d‖ ^ 2 =
        h lam - ‖d‖ ^ 2 / (2 * L) := by
      field_simp
      ring
    intro i j
    have h3 := hpair i j
    have h4 : ‖d‖ ^ 2 / (2 * L) ≤ h lam - h lam' := by linarith
    rw [div_le_iff₀ (by positivity)] at h4
    rw [div_le_iff₀ (by positivity)]
    nlinarith

end Proof

end Lemmata.CGImprovements
