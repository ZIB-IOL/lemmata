module

public import Lemmata.FrankWolfePS.Upper.FW
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem three_point (c x w : E) :
    2 * ⟪x - c, x - w⟫ = ‖x - c‖ ^ 2 + ‖x - w‖ ^ 2 - ‖c - w‖ ^ 2 := by
  have e : c - w = (x - w) - (x - c) := by abel
  have h := norm_sub_sq_real (x - w) (x - c)
  rw [← e] at h
  linarith only [h, real_inner_comm (x - w) (x - c)]

/-- Lan–Zhou outer step, derived directly from the model and the Wolfe
certificate of the returned proximal point. -/
theorem sliding_step {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} {g : E → E} {L : ℝ}
    (mdl : Models K f g L) {c y x w : E} (hc : c ∈ K) (hy : y ∈ K) (hx : x ∈ K) (hw : w ∈ K)
    {γ τ η : ℝ} (hγ : 0 ≤ γ) (hγ' : γ ≤ 1) (major : L * γ ≤ τ)
    (cert : ⟪g (blend γ y c) + τ • (x - c), x - w⟫ ≤ η) :
    f (blend γ y x) - f w ≤ (1 - γ) * (f y - f w) + γ * η +
      γ * τ / 2 * (‖c - w‖ ^ 2 - ‖x - w‖ ^ 2) := by
  let z := blend γ y c
  let v := blend γ y x
  have hz : z ∈ K := blend_mem hK hγ hγ' hy hc
  have hv : v ∈ K := blend_mem hK hγ hγ' hy hx
  have Hu := mdl.upper z hz v hv
  have yl := mdl.lower z hz y hy
  have wl := mdl.lower z hz w hw
  have id : ⟪g z, v - z⟫ = (1 - γ) * ⟪g z, y - z⟫ + γ * ⟪g z, w - z⟫ + γ * ⟪g z, x - w⟫ := by
    dsimp only [v, blend]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]; ring
  rw [id, show v - z = γ • (x - c) from blend_diff _ _ _ _, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hγ] at Hu
  change ⟪g z + τ • (x - c), x - w⟫ ≤ η at cert
  rw [inner_add_left, real_inner_smul_left] at cert
  have Hc := mul_le_mul_of_nonneg_left cert hγ
  have rem := mul_le_mul_of_nonneg_right major (mul_nonneg hγ (_root_.sq_nonneg ‖x - c‖))
  have id3 := congrArg (fun a : ℝ => γ * τ / 2 * a) (three_point c x w)
  change f v - _ ≤ _
  linarith only [Hu, mul_le_mul_of_nonneg_left yl (sub_nonneg.mpr hγ'),
    mul_le_mul_of_nonneg_left wl hγ, Hc, rem, id3]

noncomputable def gamma (j : ℕ) : ℝ := 3 / ((j : ℝ) + 2)
noncomputable def tau (L : ℝ) (j : ℕ) : ℝ := 3 * L / ((j : ℝ) + 1)
noncomputable def eta (L A : ℝ) (j : ℕ) : ℝ := L * A / ((j : ℝ) * ((j : ℝ) + 1))

theorem sliding_parameters {L A : ℝ} (hL : 0 < L) (hA : 0 < A) {j : ℕ} (hj : 0 < j) :
    0 < gamma j ∧ gamma j ≤ 1 ∧ L * gamma j ≤ tau L j ∧ 0 < tau L j ∧ 0 < eta L A j := by
  have jpos : 0 < (j : ℝ) := by exact_mod_cast hj
  have jone : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  unfold gamma tau eta
  refine ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith), ?_, by positivity,
    by positivity⟩
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Weighted scalar telescoping. The distance term is retained until the last step. -/
theorem sliding_potential {L A : ℝ} (hL : 0 ≤ L) (gap d : ℕ → ℝ)
    (dw : ∀ j, d j ≤ A)
    (rec : ∀ j, gap (j + 1) ≤ (1 - gamma (j + 1)) * gap j + gamma (j + 1) * eta L A (j + 1) +
      gamma (j + 1) * tau L (j + 1) / 2 * (d j - d (j + 1))) (n : ℕ) :
    (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * gap n + 9 * L / 2 * (n : ℝ) * d n ≤ (n : ℝ) *
        (15 * L * A / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let j : ℝ := (n : ℝ) + 1
    have hj : 0 < j := by dsimp [j]; positivity
    let W := j * (j + 1) * (j + 2)
    have H := mul_le_mul_of_nonneg_left (rec n) (show 0 ≤ W by dsimp [W]; positivity)
    have h1 : W * (1 - gamma (n + 1)) = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      dsimp [W, j, gamma]; push_cast; field_simp; ring
    have h2 : W * (gamma (n + 1) * eta L A (n + 1)) = 3 * L * A := by
      dsimp [W, j, gamma, eta]; push_cast; field_simp
    have h3 : W * (gamma (n + 1) * tau L (n + 1) / 2) = 9 * L / 2 * j := by
      dsimp [W, j, gamma, tau]; push_cast; field_simp; ring
    rw [mul_add, mul_add, ← mul_assoc, h1, h2, ← mul_assoc, h3] at H
    have bound := mul_le_mul_of_nonneg_left (dw n) (show 0 ≤ 9 * L / 2 by positivity)
    rw [Nat.cast_succ]
    change W * gap (n + 1) + 9 * L / 2 * j * d (n + 1) ≤ j * (15 * L * A / 2)
    dsimp only [j] at * ; linarith only [H, ih, bound]

theorem sliding_rate {L A : ℝ} (hL : 0 ≤ L) (gap d : ℕ → ℝ) (dn : ∀ j, 0 ≤ d j)
    (dw : ∀ j, d j ≤ A)
    (rec : ∀ j, gap (j + 1) ≤ (1 - gamma (j + 1)) * gap j + gamma (j + 1) * eta L A (j + 1) +
      gamma (j + 1) * tau L (j + 1) / 2 * (d j - d (j + 1))) {n : ℕ} (hn : 0 < n) :
    gap n ≤ 15 * L * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have h := sliding_potential hL gap d dw rec n
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd := mul_nonneg (show 0 ≤ 9 * L / 2 * (n : ℝ) by positivity) (dn n)
  apply (le_div_iff₀ (by positivity)).mpr
  apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hnp
  linarith only [h, hd]

theorem sliding_count {δ A : ℝ} (calls : ℕ → ℕ) (h0 : calls 0 = 0)
    (step : ∀ j, (calls (j + 1) : ℝ) ≤ calls j + 1 + 18 * ((j : ℝ) + 1) * δ ^ 2 / A) (n : ℕ) :
    (calls n : ℝ) ≤ n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have H := step n
    push_cast
    simp only [div_eq_mul_inv] at H ih ⊢
    linarith only [H, ih]

end Lemmata.FrankWolfePS.Upper
