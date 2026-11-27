module

public import Lemmata.FrankWolfePS.Upper.Geometry
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two first-order inequalities on the domain are the only objective
properties used by either upper algorithm. -/
structure Models (K : Set E) (f : E → ℝ) (g : E → E) (L : ℝ) : Prop where
  lower : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ ≤ f y
  upper : ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2

noncomputable def fwStepSize (j : ℕ) : ℝ := 2 / ((j : ℝ) + 2)

theorem stepSize_bounds (j : ℕ) : 0 ≤ fwStepSize j ∧ fwStepSize j ≤ 1 := by
  unfold fwStepSize
  have hj : 0 ≤ (j : ℝ) := by positivity
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩

/-- Second component counts calls to the original body oracle made by the
supplied simulation. One core request costs either zero or one actual call. -/
noncomputable def fwRun (g oracle : E → E) (cost : E → ℕ) (start : E) : ℕ → E × ℕ
  | 0 => (start, 0)
  | j + 1 => let v := fwRun g oracle cost start j
           let q := g v.1
           (blend (fwStepSize j) v.1 (oracle q), v.2 + cost q)

theorem fwRun_mem {K : Set E} (hK : Convex ℝ K) (O : LMO K) (g : E → E) (cost : E → ℕ)
    {p : E} (hp : p ∈ K) (n : ℕ) : (fwRun g O.query cost p n).1 ∈ K := by
  induction n with
  | zero => exact hp
  | succ j ih => exact blend_mem hK (stepSize_bounds j).1 (stepSize_bounds j).2 ih (O.mem _)

theorem fwRun_cost (g o : E → E) (cost : E → ℕ) (hc : ∀ q, cost q ≤ 1) (p : E) (n : ℕ) :
    (fwRun g o cost p n).2 ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ j ih => exact Nat.add_le_add ih (hc _)

theorem fw_one_step {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} {g : E → E} {L δ : ℝ}
    (model : Models K f g L) (hL : 0 ≤ L) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ) (O : LMO K)
    {x w : E} (hx : x ∈ K) (hw : w ∈ K) {t : ℝ} (ht : 0 ≤ t) (h1 : t ≤ 1) :
    f (blend t x (O.query (g x))) - f w ≤ (1 - t) * (f x - f w) + (L * δ ^ 2) / 2 * t ^ 2 := by
  let v := O.query (g x)
  have hv : v ∈ K := O.mem _
  have hlow := model.lower _ hx _ hw
  have hlin : ⟪g x, v - x⟫ ≤ f w - f x := by
    rw [inner_sub_right] at hlow ⊢
    linarith [O.least (g x) w hw]
  have h := model.upper _ hx _ (blend_mem hK ht h1 hx hv)
  rw [blend_sub, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at h
  have hs := pow_le_pow_left₀ (norm_nonneg (v - x)) (width _ hv _ hx) 2
  have hq := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (L / 2) * t ^ 2)
  change f (blend t x v) - f w ≤ _
  linarith only [h, mul_le_mul_of_nonneg_left hlin ht, hq]

/-- Scalar recurrence for first full step followed by 2/(j+2). -/
theorem fw_rate_scalar (h : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (step : ∀ j, h (j + 1) ≤ (1 - fwStepSize j) * h j + C / 2 * (fwStepSize j) ^ 2) (n : ℕ) :
    h (n + 1) ≤ 2 * C / ((n : ℝ) + 3) := by
  induction n with
  | zero =>
    have H := step 0
    norm_num [fwStepSize] at H ⊢
    linarith
  | succ n ih =>
    have e := step (n + 1)
    have m := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (stepSize_bounds (n + 1)).2)
    apply e.trans
    apply (add_le_add m (le_refl _)).trans
    simp only [fwStepSize, Nat.cast_succ]
    have hp : 0 < (n : ℝ) + 1 + 2 := by positivity
    have hq : 0 < (n : ℝ) + 3 := by positivity
    have hr : 0 < (n : ℝ) + 1 + 3 := by positivity
    field_simp
    nlinarith [mul_nonneg hC (show 0 ≤ (n : ℝ) by positivity)]

theorem fw_rate {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} {g : E → E} {L δ : ℝ}
    (model : Models K f g L) (hL : 0 ≤ L) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ) (O : LMO K)
    (cost : E → ℕ) {p w : E} (hp : p ∈ K) (hw : w ∈ K) (n : ℕ) :
    f (fwRun g O.query cost p (n + 1)).1 - f w ≤ 2 * (L * δ ^ 2) / ((n : ℝ) + 3) := by
  apply fw_rate_scalar (fun j => f (fwRun g O.query cost p j).1 - f w) (by positivity)
  intro j
  exact fw_one_step hK model hL width O (fwRun_mem hK O g cost hp j) hw
    (stepSize_bounds j).1 (stepSize_bounds j).2

end Lemmata.FrankWolfePS.Upper
