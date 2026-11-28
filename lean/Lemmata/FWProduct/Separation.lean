module

public import Lemmata.FWProduct.Objective
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# Separation at distance

If every point of the affine hull of a finite set `F` is at distance at least `δ` from the convex
hull of a finite set `K`, a single unit vector `u` separates them with margin `δ`:
`⟨u, a - q⟩ ≥ δ` for all `a ∈ aff F` and `q ∈ conv K`. The vector is the residual of the point of
`conv K` closest to `aff F`, measured orthogonally to the direction of `aff F`.
-/

namespace Lemmata.FWProduct

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_separation {F K : Finset E} (hF : F.Nonempty) (hK : K.Nonempty) {δ : ℝ}
    (hδ : ∀ a ∈ affineSpan ℝ (↑F : Set E), ∀ q ∈ convexHull ℝ (↑K : Set E), δ ≤ ‖a - q‖) :
    ∃ w : E, ‖w‖ ≤ 1 ∧ ∀ a ∈ affineSpan ℝ (↑F : Set E), ∀ q ∈ convexHull ℝ (↑K : Set E),
      δ ≤ inner ℝ w (a - q) := by
  rcases le_or_gt δ 0 with hδ0 | hδ0
  · exact ⟨0, by simp, fun a _ q _ => by simpa using hδ0⟩
  set D := vectorSpan ℝ (↑F : Set E) with hD
  have : FiniteDimensional ℝ D := finiteDimensional_vectorSpan_of_finite ℝ F.finite_toSet
  have : CompleteSpace D := FiniteDimensional.complete ℝ D
  obtain ⟨a₀, ha₀⟩ := hF
  have ha₀A : a₀ ∈ affineSpan ℝ (↑F : Set E) := subset_affineSpan ℝ _ (Finset.mem_coe.mpr ha₀)
  set z : E → E := fun y => (y - a₀) - D.starProjection (y - a₀) with hz
  have hzc : Continuous z := by
    simp only [hz]
    exact (continuous_id.sub continuous_const).sub
      (D.starProjection.continuous.comp (continuous_id.sub continuous_const))
  have hzaff : ∀ y y' : E, z y' - z y = (y' - y) - D.starProjection (y' - y) := by
    intro y y'
    simp only [hz, map_sub]; abel
  set Kc := convexHull ℝ (↑K : Set E) with hKc
  have hKcc : IsCompact Kc := Set.Finite.isCompact_convexHull (𝕜 := ℝ) K.finite_toSet
  have hKne : Kc.Nonempty := by
    obtain ⟨q, hq⟩ := hK
    exact ⟨q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq)⟩
  obtain ⟨qs, hqs, hmin⟩ := hKcc.exists_isMinOn hKne (continuous_norm.comp hzc).continuousOn
  set w := z qs with hw
  -- `‖w‖ ≥ δ`
  have hwδ : δ ≤ ‖w‖ := by
    have hmem : D.starProjection (qs - a₀) + a₀ ∈ affineSpan ℝ (↑F : Set E) := by
      have := AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact D.starProjection_apply_mem (qs - a₀)) ha₀A
      rwa [vadd_eq_add] at this
    have h := hδ _ hmem qs hqs
    have e : D.starProjection (qs - a₀) + a₀ - qs = -w := by
      simp only [hw, hz]; abel
    rw [e, norm_neg] at h
    exact h
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hδ0 hwδ
  have hworth : w ∈ Dᗮ := D.sub_starProjection_mem_orthogonal _
  -- first-order condition: `⟨w, z q - w⟩ ≥ 0` on `conv K`
  have hfo : ∀ q ∈ Kc, 0 ≤ inner ℝ w (z q - w) := by
    intro q hq
    set d := z q - w with hd
    by_contra hneg
    push Not at hneg
    set c := inner ℝ w d with hc
    set t := min 1 (-c / (‖d‖ ^ 2 + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htd : t * ‖d‖ ^ 2 ≤ -c := by
      have h1 : t ≤ -c / (‖d‖ ^ 2 + 1) := min_le_right _ _
      have h2 : t * (‖d‖ ^ 2 + 1) ≤ -c := by rwa [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hqt : qs + t • (q - qs) ∈ Kc :=
      (convex_convexHull ℝ _).add_smul_sub_mem hqs hq ⟨ht0.le, ht1⟩
    have hmin' : ‖z qs‖ ≤ ‖z (qs + t • (q - qs))‖ := hmin hqt
    have hzt : z (qs + t • (q - qs)) = w + t • d := by
      have h1 := hzaff qs (qs + t • (q - qs))
      have h2 := hzaff qs q
      rw [add_sub_cancel_left, map_smul] at h1
      calc z (qs + t • (q - qs)) = z qs + (t • (q - qs) - t • D.starProjection (q - qs)) := by
            rw [← h1]; abel
        _ = z qs + t • (z q - z qs) := by rw [h2, smul_sub t (q - qs) (D.starProjection (q - qs))]
        _ = w + t • d := rfl
    rw [hzt] at hmin'
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hmin' 2
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, inner_smul_right] at hsq
    nlinarith
  refine ⟨-(1 / ‖w‖) • w, ?_, fun a ha q hq => ?_⟩
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity), one_div,
      inv_mul_cancel₀ hw0.ne']
  · have hav : a - a₀ ∈ D := by
      rw [hD, ← direction_affineSpan]; exact AffineSubspace.vsub_mem_direction ha ha₀A
    have h1 : inner ℝ w (q - a) = inner ℝ w (z q) := by
      have e : q - a = z q + D.starProjection (q - a₀) - (a - a₀) := by simp only [hz]; abel
      rw [e, inner_sub_right, inner_add_right,
        D.inner_left_of_mem_orthogonal (D.starProjection_apply_mem _) hworth,
        D.inner_left_of_mem_orthogonal hav hworth]
      ring
    have h2 : ‖w‖ ^ 2 ≤ inner ℝ w (q - a) := by
      rw [h1]
      have := hfo q hq
      rw [inner_sub_right, real_inner_self_eq_norm_sq] at this
      linarith
    have key : inner ℝ (-(1 / ‖w‖) • w) (a - q) = 1 / ‖w‖ * inner ℝ w (q - a) := by
      rw [inner_smul_left, conj_trivial, show a - q = -(q - a) by abel, inner_neg_right]; ring
    rw [key]
    calc δ ≤ ‖w‖ := hwδ
      _ = 1 / ‖w‖ * ‖w‖ ^ 2 := by field_simp
      _ ≤ 1 / ‖w‖ * inner ℝ w (q - a) := mul_le_mul_of_nonneg_left h2 (by positivity)

end Lemmata.FWProduct
