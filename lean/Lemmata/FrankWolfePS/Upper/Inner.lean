module

public import Lemmata.FrankWolfePS.Upper.FW
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def prox (q c : E) (τ : ℝ) (x : E) : ℝ := ⟪q, x⟫ + τ / 2 * ‖x - c‖ ^ 2
def proxGrad (q c : E) (τ : ℝ) (x : E) := q + τ • (x - c)

theorem prox_taylor (q c : E) (τ : ℝ) (x y : E) :
    prox q c τ y = prox q c τ x + ⟪proxGrad q c τ x, y - x⟫ + τ / 2 * ‖y - x‖ ^ 2 := by
  unfold prox proxGrad
  rw [show y - c = (x - c) +
      (y - x) by abel, norm_add_sq_real, inner_add_left, real_inner_smul_left, inner_sub_right q]
  ring

theorem prox_models (q c : E) {τ : ℝ} (hτ : 0 ≤ τ) (K : Set E) :
    Models K (prox q c τ) (proxGrad q c τ) τ := by
  constructor
  · intro x _ y _
    rw [prox_taylor q c τ x y]
    linarith [mul_nonneg (by positivity : 0 ≤ τ / 2) (_root_.sq_nonneg ‖y - x‖)]
  · intro x _ y _; exact (prox_taylor q c τ x y).le

theorem prox_atom_gap {K : Set E} (O : LMO K) {δ τ : ℝ}
    (hτ : 0 ≤ τ) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ)
    (q c x : E) (hx : x ∈ K) {w : E} (hw : w ∈ K) :
    let v := O.query (proxGrad q c τ x)
    ⟪proxGrad q c τ v, v - w⟫ ≤ τ * δ ^ 2 := by
  let v := O.query (proxGrad q c τ x)
  have hv : v ∈ K := O.mem _
  have h : proxGrad q c τ v = proxGrad q c τ x + τ • (v - x) := by
    unfold proxGrad; rw [show v - c = (x - c) + (v - x) by abel, smul_add]; abel
  change ⟪proxGrad q c τ v, v - w⟫ ≤ _
  rw [h, inner_add_left, real_inner_smul_left]
  have base : ⟪proxGrad q c τ x, v - w⟫ ≤ 0 := by
    rw [inner_sub_right]; linarith [O.least (proxGrad q c τ x) w hw]
  have posδ := (norm_nonneg _).trans (width v hv x hx)
  have ch := (real_inner_le_norm (v - x) (v - w)).trans
    (mul_le_mul (width v hv x hx) (width v hv w hw) (norm_nonneg _) posδ)
  nlinarith [mul_le_mul_of_nonneg_left ch hτ]

end Lemmata.FrankWolfePS.Upper
