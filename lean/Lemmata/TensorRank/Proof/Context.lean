module

public import Lemmata.TensorRank.Proof.Asymptotic
public import Lemmata.TensorRank.Proof.Maps
public import Lemmata.TensorRank.Proof.IndexedProduct
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

open Classical

namespace Lemmata.TensorRank.Tensor

variable {I : Type} [Fintype I] {V W U Z : I → Type}
variable [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]
variable [∀ i, Fintype (U i)] [∀ i, Fintype (Z i)]

theorem asymptoticRank_product_assoc (S : Tensor ℂ I V) (T : Tensor ℂ I W)
    (H : Tensor ℂ I U) :
    asymptoticRank (product (product S T) H) = asymptoticRank (product S (product T H)) := by
  have he : reindex (fun i => Equiv.prodAssoc (V i) (W i) (U i))
      (product S (product T H)) = product (product S T) H := by
    funext x
    exact (mul_assoc _ _ _).symm
  rw [← he, asymptoticRank_reindex]

theorem asymptoticRank_product_comm (S : Tensor ℂ I V) (T : Tensor ℂ I W) :
    asymptoticRank (product S T) = asymptoticRank (product T S) := by
  have he : reindex (fun i => Equiv.prodComm (V i) (W i)) (product T S) = product S T := by
    funext x
    exact mul_comm _ _
  rw [← he, asymptoticRank_reindex]

def ContextLE (c : ℝ) (S : Tensor ℂ I V) (T : Tensor ℂ I W) : Prop :=
  ∀ (U : I → Type) [∀ i, Fintype (U i)] (H : Tensor ℂ I U),
    asymptoticRank (product S H) ≤ c * asymptoticRank (product T H)

theorem ContextLE.refl (S : Tensor ℂ I V) : ContextLE 1 S S := by
  intro U _ H
  simp

theorem Restricts.contextLE {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    (h : Restricts S T) : ContextLE 1 S T := by
  intro U _ H
  simpa only [one_mul] using (h.product (Restricts.refl H)).asymptoticRank_le

theorem ContextLE.trans {c d : ℝ} {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    {Q : Tensor ℂ I U} (h : ContextLE c S T) (g : ContextLE d T Q) (hc : 0 ≤ c) :
    ContextLE (c * d) S Q := by
  intro Z _ H
  calc
    asymptoticRank (product S H) ≤ c * asymptoticRank (product T H) := h _ H
    _ ≤ c * (d * asymptoticRank (product Q H)) := mul_le_mul_of_nonneg_left (g _ H) hc
    _ = _ := (mul_assoc _ _ _).symm

theorem ContextLE.rightTensor {c : ℝ} {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    (h : ContextLE c S T) (Q : Tensor ℂ I U) : ContextLE c (product S Q) (product T Q) := by
  intro Z _ H
  simpa only [asymptoticRank_product_assoc] using h _ (product Q H)

theorem ContextLE.leftTensor {c : ℝ} {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    (h : ContextLE c S T) (Q : Tensor ℂ I U) : ContextLE c (product Q S) (product Q T) := by
  intro Z _ H
  have hr (X : I → Type) [∀ i, Fintype (X i)] (A : Tensor ℂ I X) :
      asymptoticRank (product (product Q A) H) = asymptoticRank (product A (product Q H)) := by
    let e (i : I) :=
      (Equiv.prodCongr (Equiv.prodComm (U i) (X i)) (Equiv.refl (Z i))).trans
        (Equiv.prodAssoc (X i) (U i) (Z i))
    have he : reindex (fun i => e i) (product A (product Q H)) = product (product Q A) H := by
      funext x
      change A (fun i => (x i).1.2) * (Q (fun i => (x i).1.1) * H (fun i => (x i).2)) = _
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
    rw [← he, asymptoticRank_reindex]
  simpa only [hr] using h _ (product Q H)

theorem ContextLE.product {c d : ℝ} {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    {A : Tensor ℂ I U} {B : Tensor ℂ I Z}
    (h : ContextLE c S T) (g : ContextLE d A B) (hc : 0 ≤ c) :
    ContextLE (c * d) (product S A) (product T B) :=
  (h.rightTensor A).trans (g.leftTensor T) hc

theorem asymptoticRank_product_reindex (S : Tensor ℂ I V) (H : Tensor ℂ I U)
    (e : ∀ i, W i ≃ V i) :
    asymptoticRank (product (reindex (fun i => e i) S) H) = asymptoticRank (product S H) := by
  have he : reindex (fun i => Equiv.prodCongr (e i) (Equiv.refl (U i))) (product S H) =
      product (reindex (fun i => e i) S) H := rfl
  rw [← he, asymptoticRank_reindex]

theorem contextLE_reindex_iff {c : ℝ} (S : Tensor ℂ I V) (T : Tensor ℂ I U)
    (e : ∀ i, W i ≃ V i) (f : ∀ i, Z i ≃ U i) :
    ContextLE c (reindex (fun i => e i) S) (reindex (fun i => f i) T) ↔ ContextLE c S T := by
  constructor <;> intro h X _ H
  · simpa only [asymptoticRank_product_reindex] using h X H
  · simpa only [asymptoticRank_product_reindex] using h X H

theorem ContextLE.of_reindex {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    (e : ∀ i, W i ≃ V i) (h : reindex (fun i => e i) S = T) : ContextLE 1 S T := by
  have hs : reindex (fun i => (e i).symm) T = S := by
    rw [← h]
    funext x
    simp [reindex]
  rw [← hs]
  exact (reindex_restricts _ _).contextLE

theorem ContextLE.asymptoticRank_le {c : ℝ} {S : Tensor ℂ I V} {T : Tensor ℂ I W}
    (h : ContextLE c S T) : asymptoticRank S ≤ c * asymptoticRank T := by
  let H : Tensor ℂ I (fun _ => PUnit) := fun _ => 1
  have hunit (X : I → Type) [∀ i, Fintype (X i)] (A : Tensor ℂ I X) :
      asymptoticRank (Lemmata.TensorRank.Tensor.product A H) = asymptoticRank A := by
    have he : reindex (fun i => Equiv.prodPUnit (X i)) A = Lemmata.TensorRank.Tensor.product A H := by
      funext x
      simp [reindex, Lemmata.TensorRank.Tensor.product, H]
    rw [← he, asymptoticRank_reindex]
  simpa only [hunit] using h _ H

theorem ContextLE.indexedProduct_fin : ∀ {n : ℕ}
    {V W : Fin n → I → Type} [∀ j i, Fintype (V j i)] [∀ j i, Fintype (W j i)]
    {S : ∀ j, Tensor ℂ I (V j)} {T : ∀ j, Tensor ℂ I (W j)} {c : Fin n → ℝ},
    (∀ j, ContextLE (c j) (S j) (T j)) → (∀ j, 0 ≤ c j) →
      ContextLE (∏ j, c j) (indexedProduct S) (indexedProduct T) := by
  intro n
  induction n with
  | zero =>
      intro V W _ _ S T c h hc
      have he : reindex (fun i => Equiv.ofUnique (∀ j : Fin 0, V j i) (∀ j : Fin 0, W j i))
          (indexedProduct T) = indexedProduct S := by
        funext x
        simp [reindex, indexedProduct]
      simp only [Fin.prod_univ_zero]
      rw [← he]
      exact (reindex_restricts _ _).contextLE
  | succ n ih =>
      intro V W _ _ S T c h hc
      let e (i : I) := Fin.consEquiv (fun j => V j i)
      let f (i : I) := Fin.consEquiv (fun j => W j i)
      have he : reindex (fun i => e i) (indexedProduct S) =
          Lemmata.TensorRank.Tensor.product (S 0) (indexedProduct (fun j : Fin n => S j.succ)) := by
        funext x
        simp [reindex, indexedProduct, Lemmata.TensorRank.Tensor.product, e, Fin.consEquiv, Fin.prod_univ_succ]
      have hf : reindex (fun i => f i) (indexedProduct T) =
          Lemmata.TensorRank.Tensor.product (T 0) (indexedProduct (fun j : Fin n => T j.succ)) := by
        funext x
        simp [reindex, indexedProduct, Lemmata.TensorRank.Tensor.product, f, Fin.consEquiv, Fin.prod_univ_succ]
      apply (contextLE_reindex_iff _ _ e f).mp
      rw [he, hf, Fin.prod_univ_succ]
      exact (h 0).product (ih (fun j => h j.succ) (fun j => hc j.succ)) (hc 0)

end Lemmata.TensorRank.Tensor
