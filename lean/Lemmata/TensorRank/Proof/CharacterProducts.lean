module

public import Lemmata.TensorRank.Proof.Characters
public import Lemmata.TensorRank.Proof.WordSectors
public import Lemmata.TensorRank.Proof.WeightedGraph
public import Lemmata.TensorRank.Proof.PairingGraph

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring.Character

variable {k : ℕ} (f : Character k)

theorem eval_indexedProduct_fin (N : ℕ) {U : Fin N → Fin k → Type}
    [∀ j i, Fintype (U j i)] (T : ∀ j, Tensor ℂ (Fin k) (U j)) :
    f.eval (Tensor.indexedProduct T) = ∏ j, f.eval (T j) := by
  induction N with
  | zero =>
      have he : ofTensor (Tensor.indexedProduct T) = (1 : Value k) := by
        apply Quot.sound
        apply Object.equivalent_of_reindex _ _
          (fun i => Equiv.ofUnique PUnit (∀ j : Fin 0, U j i))
        funext x
        simp [Tensor.reindex, Tensor.indexedProduct, Object.one]
      simp only [eval, he, map_one, Fin.prod_univ_zero]
  | succ N ih =>
      let e := fun i => Fin.consEquiv (fun j : Fin (N + 1) => U j i)
      have hp : Tensor.reindex (fun i => e i) (Tensor.indexedProduct T) =
          Tensor.product (T 0) (Tensor.indexedProduct (fun j : Fin N => T j.succ)) := by
        funext x
        simp [Tensor.reindex, Tensor.indexedProduct, Tensor.product, e,
          Fin.consEquiv, Fin.prod_univ_succ]
      rw [← eval_reindex f e (Tensor.indexedProduct T), hp, eval_product, ih, Fin.prod_univ_succ]

theorem eval_indexedProduct {J : Type} [Fintype J] {U : J → Fin k → Type}
    [∀ j i, Fintype (U j i)] (T : ∀ j, Tensor ℂ (Fin k) (U j)) :
    f.eval (Tensor.indexedProduct T) = ∏ j, f.eval (T j) := by
  let e := (Fintype.equivFin J).symm
  let c := fun i => Equiv.piCongrLeft (fun j => U j i) e
  have hp : Tensor.reindex (fun i => c i) (Tensor.indexedProduct T) =
      Tensor.indexedProduct (fun j => T (e j)) := by
    funext x
    change (∏ j : J, T j (fun i => c i (x i) j)) =
      ∏ j : Fin (Fintype.card J), T (e j) (fun i => x i j)
    symm
    apply Fintype.prod_equiv e
    intro j
    congr 1
    funext i
    exact (Equiv.piCongrLeft_apply_apply (fun j => U j i) e (x i) j).symm
  rw [← eval_reindex f c (Tensor.indexedProduct T), hp, eval_indexedProduct_fin]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem eval_wordTensor {C : Type} [Fintype C] {N : ℕ}
    {V : Fin k → Type} [∀ i, Fintype (V i)]
    (Z : C → Tensor ℂ (Fin k) V) (w : Fin N → C) :
    f.eval (Tensor.wordTensor Z w) = ∏ c, f.eval (Z c) ^ (Types.histogram w c).val := by
  have h := f.eval_indexedProduct_fin N (fun j => Z (w j))
  rw [Types.word_weight (fun c => f.eval (Z c)) w] at h
  exact h

theorem eval_weighted_product (d e : Edge k → ℕ) :
    f.eval (weightedComplete (fun a => d a * e a)) =
      f.eval (weightedComplete d) * f.eval (weightedComplete e) := by
  rw [← eval_reindex f (weightedProductCoordinate d e) (weightedComplete (fun a => d a * e a)),
    weighted_product_reindex, eval_product]

theorem eval_weighted_indexedProduct {J : Type} [Fintype J] (d : J → Edge k → ℕ) :
    f.eval (weightedComplete (fun e => ∏ j, d j e)) =
      ∏ j, f.eval (weightedComplete (d j)) := by
  rw [← eval_reindex f (weightedIndexedCoordinate d) (weightedComplete (fun e => ∏ j, d j e)),
    weighted_indexedProduct_reindex, eval_indexedProduct]

theorem eval_weighted_eq_prod_edges (d : Edge k → ℕ) :
    f.eval (weightedComplete d) = ∏ e, f.eval (weightedComplete (singleEdgeDimensions e (d e))) := by
  have hd : (fun a => ∏ e, singleEdgeDimensions e (d e) a) = d := by
    funext a
    simp [singleEdgeDimensions]
  have h := f.eval_weighted_indexedProduct (fun e => singleEdgeDimensions e (d e))
  rw [hd] at h
  exact h

end Lemmata.TensorRank.TensorSemiring.Character
