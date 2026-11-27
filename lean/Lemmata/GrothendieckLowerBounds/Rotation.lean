module

public import Lemmata.GrothendieckLowerBounds.Statement
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public section

namespace Lemmata.GrothendieckLowerBounds

open scoped BigOperators
open MeasureTheory

private theorem sub_left {n m d : ℕ} (M : BellMatrix n m)
    (u x : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ) :
    vectorObj M (fun i k => u i k - x i k) v = vectorObj M u v - vectorObj M x v := by
  simp only [vectorObj, sub_mul, mul_sub, Finset.sum_sub_distrib]

private theorem sub_right {n m d : ℕ} (M : BellMatrix n m)
    (u : Fin n → Fin d → ℝ) (v y : Fin m → Fin d → ℝ) :
    vectorObj M u (fun j k => v j k - y j k) = vectorObj M u v - vectorObj M u y := by
  simp only [vectorObj, mul_sub, Finset.sum_sub_distrib]

private theorem scale_left {n m d : ℕ} (M : BellMatrix n m) (c : ℝ)
    (u : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ) :
    vectorObj M (fun i k => c * u i k) v = c * vectorObj M u v := by
  simp only [vectorObj, mul_assoc, ← Finset.mul_sum, mul_left_comm (M _ _) c]

private theorem scale_right {n m d : ℕ} (M : BellMatrix n m) (c : ℝ)
    (u : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ) :
    vectorObj M u (fun j k => c * v j k) = c * vectorObj M u v := by
  simp only [vectorObj, mul_left_comm (u _ _) c, ← Finset.mul_sum, mul_left_comm (M _ _) c]

/-- An ensemble of vector pairs with mixed first moments α and β, pointwise
score at most U and centered residual score at least −e Q has U ≥ (bα+aβ−ab−e)Q.
All randomness is shared through one probability space. -/
theorem averaged_vector_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n m d : ℕ} (M : BellMatrix n m)
    (x : Fin n → Fin d → ℝ) (y : Fin m → Fin d → ℝ)
    (A : Ω → Fin n → Fin d → ℝ) (B : Ω → Fin m → Fin d → ℝ)
    (a b α β e U : ℝ)
    (hA : Integrable (fun ω => vectorObj M (A ω) y) μ)
    (hB : Integrable (fun ω => vectorObj M x (B ω)) μ)
    (hα : ∫ ω, vectorObj M (A ω) y ∂μ = α * vectorObj M x y)
    (hβ : ∫ ω, vectorObj M x (B ω) ∂μ = β * vectorObj M x y)
    (hU : ∀ ω, vectorObj M (A ω) (B ω) ≤ U)
    (he : ∀ ω, -e * vectorObj M x y ≤ vectorObj M
      (fun i k => A ω i k - a * x i k) (fun j k => B ω j k - b * y j k)) :
    (b * α + a * β - a * b - e) * vectorObj M x y ≤ U := by
  have hpoint (ω : Ω) :
      b * vectorObj M (A ω) y + a * vectorObj M x (B ω) ≤
        U + (a * b + e) * vectorObj M x y := by
    have hr := he ω
    rw [sub_left, sub_right, sub_right, scale_left, scale_right,
      scale_right, scale_left] at hr
    linarith only [hU ω, hr]
  have hi := integral_mono ((hA.const_mul b).add (hB.const_mul a)) (integrable_const _) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hA.const_mul b) (hB.const_mul a), integral_const_mul,
    integral_const_mul, hα, hβ] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  linarith only [hi]

private theorem rescale_ball {n d : ℕ} (u : Fin n → Fin d → ℝ) (t r : ℝ)
    (ht : t ^ 2 * r ^ 2 = 1) (hu : ∀ i, ∑ k, u i k ^ 2 ≤ r ^ 2) :
    ∀ i, ∑ k, (t * u i k) ^ 2 ≤ 1 := by
  intro i
  simp only [mul_pow, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (hu i) (sq_nonneg t)).trans_eq ht

private theorem residual_lower {n m d : ℕ} (M : BellMatrix n m) (Q : ℝ)
    (hmax : ∀ u v, (∀ i, ∑ k : Fin d, u i k ^ 2 ≤ (1 : ℝ)) →
      (∀ j, ∑ k : Fin d, v j k ^ 2 ≤ (1 : ℝ)) → vectorObj M u v ≤ Q)
    (u : Fin n → Fin d → ℝ) (v : Fin m → Fin d → ℝ)
    (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (hu : ∀ i, ∑ k, u i k ^ 2 ≤ s ^ 2) (hv : ∀ j, ∑ k, v j k ^ 2 ≤ δ ^ 2) :
    -(s * δ) * Q ≤ vectorObj M u v := by
  have ha := rescale_ball u (-1 / s) s (by field_simp) hu
  have hb := rescale_ball v (1 / δ) δ (by field_simp) hv
  have hm := hmax _ _ ha hb
  rw [scale_left, scale_right] at hm
  have h := mul_le_mul_of_nonneg_left hm (mul_nonneg hs.le hδ.le)
  rw [show s * δ * (-1 / s * (1 / δ * vectorObj M u v)) = -vectorObj M u v by
    field_simp] at h
  linarith only [h]

/-- Uniform numerical bound on each order-three Bell ratio. The finite local
model supplies the pointwise score bound. The spherical argument supplies the
two mixed moments and the pointwise deviation estimates. -/
theorem order_three_rotation_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n m : ℕ} (M : BellMatrix n m)
    (x : Fin n → Fin 3 → ℝ) (y : Fin m → Fin 3 → ℝ)
    (A : Ω → Fin n → Fin 3 → ℝ) (B : Ω → Fin m → Fin 3 → ℝ) (C α β : ℝ)
    (hC : 0 < C)
    (hmax : ∀ u v, (∀ i, ∑ k : Fin 3, u i k ^ 2 ≤ (1 : ℝ)) →
      (∀ j, ∑ k : Fin 3, v j k ^ 2 ≤ (1 : ℝ)) → vectorObj M u v ≤ vectorObj M x y)
    (hA : Integrable (fun ω => vectorObj M (A ω) y) μ)
    (hB : Integrable (fun ω => vectorObj M x (B ω)) μ)
    (hα : ∫ ω, vectorObj M (A ω) y ∂μ = α * vectorObj M x y)
    (hβ : ∫ ω, vectorObj M x (B ω) ∂μ = β * vectorObj M x y) :
    let h : ℝ := 9967561175483381 / 10 ^ 16
    let w : ℝ := 6919401772871383 / 10 ^ 16
    let a : ℝ := 19 / 20
    let b := (1 + h) / 2
    let δ := (1 - h) / 2
    let s := Real.sqrt (1 - 2 * a * h + a ^ 2)
    b ≤ α → h + h ^ 3 * (1 - h) / 4 ≤ β →
    (∀ ω, vectorObj M (A ω) (B ω) ≤ C / w) →
    (∀ ω i, ∑ k, (A ω i k - a * x i k) ^ 2 ≤ s ^ 2) →
    (∀ ω j, ∑ k, (B ω j k - b * y j k) ^ 2 ≤ δ ^ 2) →
    vectorObj M x y / C ≤ 14512635753 / 10 ^ 10 := by
  intro h w a b δ s hsupport hradial hlocal hdevA hdevB
  have hs : 0 < s := Real.sqrt_pos.mpr (by norm_num [a, h])
  have hδ : 0 < δ := by norm_num [δ, h]
  have hres ω := residual_lower M _ hmax _ _ s δ hs hδ (hdevA ω) (hdevB ω)
  have havg := averaged_vector_bound μ M x y A B a b α β (s * δ) (C / w)
    hA hB hα hβ hlocal hres
  let S : ℝ := 9307726176761760540 / 10 ^ 20
  have hsS : s ≤ S := Real.sqrt_le_iff.mpr ⟨by norm_num [S], by norm_num [a, h, S]⟩
  let r := h + h ^ 3 * (1 - h) / 4
  let l := b ^ 2 + a * (r - b) - S * δ
  have hcoef : l ≤ b * α + a * β - a * b - s * δ := by
    have h₁ := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ b by norm_num [b, h])
    have h₂ := mul_le_mul_of_nonneg_left (show r ≤ β from hradial) (show 0 ≤ a by norm_num [a])
    have h₃ := mul_le_mul_of_nonneg_right hsS hδ.le
    dsimp only [l]
    linarith only [h₁, h₂, h₃]
  have hQ : 0 ≤ vectorObj M x y := by
    simpa [vectorObj] using hmax (fun _ _ => 0) (fun _ _ => 0) (by simp) (by simp)
  have hl : 0 < l := by norm_num [l, h, b, a, r, S, δ]
  have hcap : 1 / w ≤ 14512635753 / 10 ^ 10 * l := by norm_num [l, w, h, b, a, r, S, δ]
  rw [div_le_iff₀ hC]
  apply le_of_mul_le_mul_left _ hl
  calc
    l * vectorObj M x y ≤ C / w := (mul_le_mul_of_nonneg_right hcoef hQ).trans havg
    _ = C * (1 / w) := by ring
    _ ≤ C * (14512635753 / 10 ^ 10 * l) := mul_le_mul_of_nonneg_left hcap hC.le
    _ = l * (14512635753 / 10 ^ 10 * C) := by ring

end Lemmata.GrothendieckLowerBounds
