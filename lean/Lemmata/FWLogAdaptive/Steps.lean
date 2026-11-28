module

public import Lemmata.FWLogAdaptive.Product
public import Lemmata.FWAffineOpenLoop.Weak

@[expose] public section

/-!
# One step of the run

A step whose gap is below the threshold `X_i = (M g(i) η_i/(2ε))^{1/(1-r)}` leaves a gap of at most
`X_i` (strong growth) or `X_i + η_i² M/2` (weak growth); every other step contracts by
`1 - (1 - ε/g(i)) η_i`.
-/

namespace Lemmata.FWLogAdaptive

open Lemmata.FrankWolfe Lemmata.FWAffineOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two kinds of steps under strong `(M, r)`-growth, for the best duality gap. -/
theorem strong_step {C : Set E} {f : E → ℝ} {g : ℕ → ℝ} {M r ε : ℝ} {x v : ℕ → E}
    (hC : Convex ℝ C) (hM : 0 < M) (hg2 : ∀ t, 2 ≤ g t) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (hε0 : 0 < ε) (hgr : IsStrongGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (etaG g)) (i : ℕ) (hεi : ε ≤ g i) :
    (fderiv ℝ f (x i) (x i - v i) ≤ (M * g i * etaG g i / (2 * ε)) ^ (1 / (1 - r)) →
      pdGap f x v (i + 1) ≤ (M * g i * etaG g i / (2 * ε)) ^ (1 / (1 - r))) ∧
    ((M * g i * etaG g i / (2 * ε)) ^ (1 / (1 - r)) < fderiv ℝ f (x i) (x i - v i) →
      pdGap f x v (i + 1) ≤
        pdGap f x v i - (1 - ε / g i) * (etaG g i * fderiv ℝ f (x i) (x i - v i))) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hC hrun
  have h1 := pd_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hgr (x i) (hmem i) (v i) hvC hvmin (etaG g i) hγ
  rw [← hx] at h3
  have hg0 := gap_nonneg hC hrun i
  have hgi := hg2 i
  set G := fderiv ℝ f (x i) (x i - v i) with hGdef
  set η := etaG g i with hη
  have hηpos : 0 < η := etaG_pos hg2 i
  have hη1 : η ≤ 1 := hγ.2
  set a := M * g i * η / (2 * ε) with ha
  have hapos : 0 < a := by positivity
  set T := a ^ (1 / (1 - r)) with hT
  have hTpos : 0 < T := Real.rpow_pos_of_pos hapos _
  have h1r : 0 < 1 - r := by linarith
  have hT1r : T ^ (1 - r) = a := by
    rw [hT, ← Real.rpow_mul hapos.le, one_div_mul_cancel h1r.ne', Real.rpow_one]
  have hgpos : (0 : ℝ) < g i := by linarith
  have hMη : M * η ^ 2 / 2 = η * (ε / g i) * a := by rw [ha]; field_simp
  refine ⟨fun hsmall => ?_, fun hbig => ?_⟩
  · have hgr' : G ^ r ≤ T ^ r := Real.rpow_le_rpow hg0 hsmall hr0
    have hsplit : T ^ (1 - r) * T ^ r = T := by
      rw [← Real.rpow_add hTpos, sub_add_cancel, Real.rpow_one]
    have hεg : ε / g i ≤ 1 := by rw [div_le_one hgpos]; exact hεi
    have h5 : M * η ^ 2 / 2 * G ^ r ≤ η * T := by
      rw [hMη]
      calc η * (ε / g i) * a * G ^ r ≤ η * 1 * a * T ^ r := by
            apply mul_le_mul _ hgr' (Real.rpow_nonneg hg0 _) (by positivity)
            apply mul_le_mul_of_nonneg_right _ hapos.le
            exact mul_le_mul_of_nonneg_left hεg hηpos.le
        _ = η * T := by rw [mul_one, mul_assoc, ← hT1r, hsplit]
    have h6 : (1 - η) * G ≤ (1 - η) * T := mul_le_mul_of_nonneg_left hsmall (by linarith)
    have hpg := pd_le_gap f x v i
    nlinarith
  · have hGpos : 0 < G := lt_trans hTpos hbig
    have hga : a ≤ G ^ (1 - r) := by
      rw [← hT1r]; exact Real.rpow_le_rpow hTpos.le hbig.le h1r.le
    have hsplit : G ^ (1 - r) * G ^ r = G := by
      rw [← Real.rpow_add hGpos, sub_add_cancel, Real.rpow_one]
    have h5 : M * η ^ 2 / 2 * G ^ r ≤ η * (ε / g i) * G := by
      rw [hMη]
      calc η * (ε / g i) * a * G ^ r ≤ η * (ε / g i) * G ^ (1 - r) * G ^ r := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hg0 _)
            exact mul_le_mul_of_nonneg_left hga (by positivity)
        _ = η * (ε / g i) * G := by rw [mul_assoc, hsplit]
    nlinarith

/-- A small step under strong `(M, 0)`-growth. -/
theorem weak_small_step {C : Set E} {f : E → ℝ} {g : ℕ → ℝ} {M : ℝ} {x v : ℕ → E} {xStar : E}
    (hconv : ConvexOn ℝ C f) (hgr0 : IsStrongGrowth C f M 0)
    (hrun : IsFWRun C (fderiv ℝ f) x v (etaG g)) (i : ℕ) :
    f (x (i + 1)) - f xStar ≤ (f (x i) - f xStar) + etaG g i ^ 2 * M / 2 := by
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1 := f_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hgr0 (x i) (hmem i) (v i) hvC hvmin (etaG g i) hγ
  rw [Real.rpow_zero, mul_one, ← hx] at h3
  have hg := gap_nonneg hconv.1 hrun i
  have : 0 ≤ etaG g i * fderiv ℝ f (x i) (x i - v i) := mul_nonneg hγ.1 hg
  linarith

/-- A step above the threshold contracts the primal gap, under weak `(M, r)`-growth. -/
theorem weak_big_step {C : Set E} {f : E → ℝ} {g : ℕ → ℝ} {M r ε : ℝ} {x v : ℕ → E}
    {xStar : E} (hconv : ConvexOn ℝ C f) (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y)
    (hxs : xStar ∈ minimizers C f) (hM : 0 < M) (hg2 : ∀ t, 2 ≤ g t)
    (hr : r ∈ Set.Ico (0 : ℝ) 1) (hε0 : 0 < ε) (hw : IsWeakGrowth C f M r)
    (hrun : IsFWRun C (fderiv ℝ f) x v (etaG g)) (i : ℕ) (hεi : ε ≤ g i)
    (hbig : (M * g i * etaG g i / (2 * ε)) ^ (1 / (1 - r)) < f (x i) - f xStar) :
    f (x (i + 1)) - f xStar ≤ (1 - (1 - ε / g i) * etaG g i) * (f (x i) - f xStar) := by
  obtain ⟨hr0, hr1⟩ := hr
  have hmem := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun
  have h1 := f_step hrun i
  obtain ⟨hvC, hvmin, hγ, hx⟩ := hrun.2 i
  have h3 := hw (x i) (hmem i) (v i) hvC hvmin xStar hxs (etaG g i) hγ
  rw [← hx] at h3
  have hsg := subopt_le_gap hconv hdiff hxs hrun i
  have hg0 := gap_nonneg hconv.1 hrun i
  have hgi := hg2 i
  set G := fderiv ℝ f (x i) (x i - v i) with hGdef
  set h := f (x i) - f xStar with hh
  set D := bregman f (x (i + 1)) (x i) with hD
  set η := etaG g i with hη
  have hηpos : 0 < η := etaG_pos hg2 i
  have hgpos : (0 : ℝ) < g i := by linarith
  have h1r : 0 < 1 - r := by linarith
  set A := M * g i * η / (2 * ε) with hA
  have hApos : 0 < A := by positivity
  have hT : (A ^ (1 / (1 - r))) ^ (1 - r) = A := by
    rw [← Real.rpow_mul hApos.le, one_div_mul_cancel h1r.ne', Real.rpow_one]
  have hhA : A ≤ h ^ (1 - r) := by
    rw [← hT]; exact Real.rpow_le_rpow (Real.rpow_nonneg hApos.le _) hbig.le h1r.le
  have hMA : M * η ^ 2 / 2 = A * (ε / g i * η) := by rw [hA]; field_simp
  have hDle : D ≤ ε / g i * η * G := by
    rcases le_or_gt D 0 with hDn | hDp
    · have : 0 ≤ ε / g i * η * G := by positivity
      linarith
    · have h4 : D * A ≤ D * h ^ (1 - r) := mul_le_mul_of_nonneg_left hhA hDp.le
      have h5 : D * A ≤ A * (ε / g i * η * G) := by
        calc D * A ≤ D * h ^ (1 - r) := h4
          _ ≤ M * η ^ 2 / 2 * G := h3
          _ = A * (ε / g i * η * G) := by rw [hMA]; ring
      have := le_of_mul_le_mul_left (by linarith [h5] : A * D ≤ A * (ε / g i * η * G)) hApos
      linarith
  have hcoef : 0 ≤ (1 - ε / g i) * η := by
    apply mul_nonneg _ hηpos.le
    rw [sub_nonneg, div_le_one hgpos]; exact hεi
  have := mul_le_mul_of_nonneg_left hsg hcoef
  nlinarith

end Lemmata.FWLogAdaptive
