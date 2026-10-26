module

public import Lemmata.CocubicCovering.Proof.Forms
public meta import Lemmata.CocubicCovering.Proof.Forms
public import Lemmata.CocubicCovering.Proof.Polynomial
public meta import Lemmata.CocubicCovering.Proof.Polynomial
public import Lemmata.CocubicCovering.Proof.Matrix
public meta import Lemmata.CocubicCovering.Proof.Matrix

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringEmbedding

open scoped BigOperators
open Covering CoveringPolynomial CoveringCertificate

def sparseForm9 : Polynomial :=
  (CoveringMatrix.cubic ++ [{6, 7, 8}]).map fun term => CoveringMatrix.ambient \ term

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem decode_sparseForm9 : decode 9 sparseForm9 = form9 := by native_decide

theorem sparseForm9_bounded : Bounded 9 sparseForm9 := by
  unfold Bounded
  native_decide

theorem multiplier_bounded (i : Fin 24) : Bounded 9 (CoveringMatrix.multiplier i) := by
  unfold Bounded
  fin_cases i <;> native_decide

theorem multiplier_degree (i : Fin 24) :
    ∀ term ∈ CoveringMatrix.multiplier i, term.card ≤ 2 := by
  fin_cases i <;> native_decide

theorem multiplier_product_bounded (i : Fin 24) :
    Bounded 9 (multiply (CoveringMatrix.multiplier i) sparseForm9) := by
  unfold Bounded
  fin_cases i <;> native_decide

theorem multiplier_product_degree (i : Fin 24) :
    ∀ term ∈ multiply (CoveringMatrix.multiplier i) sparseForm9, term.card ≤ 7 := by
  fin_cases i <;> native_decide

def extendAssignment {m : ℕ} (x : Vector m) : ℕ → Field :=
  fun v => if h : v < m then x ⟨v, h⟩ else 0

theorem eval_decode_at {m : ℕ} (polynomial : Polynomial) (hpolynomial : Bounded m polynomial)
    (x : Vector m) :
    Covering.eval (decode m polynomial) x = evalField (extendAssignment x) polynomial := by
  have hr : (fun i : Fin m => extendAssignment x i.val) = x := by
    funext i
    simp [extendAssignment, i.isLt]
  simpa only [hr] using eval_decode m polynomial hpolynomial (extendAssignment x)

def multiplierFunction (i : Fin 24) : BooleanFunction 9 :=
  Covering.eval (decode 9 (CoveringMatrix.multiplier i))

theorem multiplier_mem (i : Fin 24) : multiplierFunction i ∈ reedMuller 9 2 :=
  decode_mem_reedMuller 9 (CoveringMatrix.multiplier i) 2 (multiplier_degree i)

theorem multiplier_product_mem (i : Fin 24) :
    multiplierFunction i * Covering.eval form9 ∈ reedMuller 9 7 := by
  have heq : Covering.eval (decode 9 (multiply (CoveringMatrix.multiplier i) sparseForm9)) =
      multiplierFunction i * Covering.eval form9 := by
    funext x
    change Covering.eval (decode 9 (multiply (CoveringMatrix.multiplier i) sparseForm9)) x =
      Covering.eval (decode 9 (CoveringMatrix.multiplier i)) x * Covering.eval form9 x
    rw [eval_decode_at _ (multiplier_product_bounded i), evalField_multiply,
      ← eval_decode_at _ (multiplier_bounded i),
      ← eval_decode_at _ sparseForm9_bounded, decode_sparseForm9]
  rw [← heq]
  exact decode_mem_reedMuller 9 (multiply (CoveringMatrix.multiplier i) sparseForm9) 7
    (multiplier_product_degree i)

def multiplierLinear : Vector 24 →ₗ[Field] BooleanFunction 9 where
  toFun a := ∑ i, a i • multiplierFunction i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum, smul_smul]

theorem multiplierLinear_mem (a : Vector 24) : multiplierLinear a ∈ reedMuller 9 2 := by
  change (∑ i : Fin 24, a i • multiplierFunction i) ∈ reedMuller 9 2
  apply (reedMuller 9 2).sum_mem
  intro i hi
  exact (reedMuller 9 2).smul_mem (a i) (multiplier_mem i)

theorem multiplierLinear_products (a : Vector 24) :
    multiplierLinear a * Covering.eval form9 ∈ reedMuller 9 7 := by
  have heq : multiplierLinear a * Covering.eval form9 =
      ∑ i : Fin 24, a i • (multiplierFunction i * Covering.eval form9) := by
    funext x
    simp [multiplierLinear, Finset.sum_mul, mul_assoc]
  rw [heq]
  apply (reedMuller 9 7).sum_mem
  intro i hi
  exact (reedMuller 9 7).smul_mem (a i) (multiplier_product_mem i)

theorem form9_weight_lower (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    20 + Module.finrank Field (LinearMap.range
      (supportGram (Covering.eval form9 + h) multiplierLinear)) ≤
        weight (Covering.eval form9 + h) := by
  have hweight := weight_bound_of_correction (by decide) (Covering.eval form9) h
    form9_mem hh multiplierLinear multiplierLinear_mem multiplierLinear_products
  have hdim := form9_affine_dimension_lower h hh
  omega

end Lemmata.CocubicCovering.CoveringEmbedding
