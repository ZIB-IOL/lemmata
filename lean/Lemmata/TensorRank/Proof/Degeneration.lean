module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.Interpolation
public import Lemmata.TensorRank.Proof.Readability
public import Lemmata.TensorRank.Proof.Parties
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

universe u v w z

variable {R : Type u} [CommRing R] {I : Type v}

theorem Leading.exists_remainder {V : I → Type w}
    {P : Tensor (Polynomial R) I V} {T : Tensor R I V} {e : ℕ}
    (h : Leading P e T) : ∃ E : Tensor (Polynomial R) I V, ∀ x,
      P x = Polynomial.X ^ e * Polynomial.C (T x) + Polynomial.X ^ (e + 1) * E x := by
  have hd (x : ∀ i, V i) :
      Polynomial.X ^ (e + 1) ∣ P x - Polynomial.C (T x) * Polynomial.X ^ e := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro j hj
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    by_cases he : j = e
    · subst j
      rw [ite_eq_left rfl, show (P x).coeff e = T x from congrFun h.1 x, sub_self]
    · have hj' : j < e := by omega
      rw [ite_eq_right he, show (P x).coeff j = 0 from congrFun (h.2 j hj') x, sub_self]
  choose E hE using hd
  refine ⟨E, ?_⟩
  intro x
  have hx := (sub_eq_iff_eq_add).mp (hE x)
  rw [hx]
  ring

theorem Leading.of_remainder {V : I → Type w}
    {P : Tensor (Polynomial R) I V} {T : Tensor R I V} {e : ℕ}
    (E : Tensor (Polynomial R) I V)
    (h : ∀ x, P x = Polynomial.X ^ e * Polynomial.C (T x) +
      Polynomial.X ^ (e + 1) * E x) : Leading P e T := by
  constructor
  · funext x
    change (P x).coeff e = T x
    rw [h x, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
    simp
  · intro j hj
    funext x
    change (P x).coeff j = 0
    rw [h x, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
    simp only [not_le.mpr hj, ite_false, not_le.mpr (by omega : j < e + 1), add_zero]

theorem Leading.product {V : I → Type w} {W : I → Type z}
    {P : Tensor (Polynomial R) I V} {Q : Tensor (Polynomial R) I W}
    {S : Tensor R I V} {T : Tensor R I W} {e f : ℕ}
    (hP : Leading P e S) (hQ : Leading Q f T) :
    Leading (Lemmata.TensorRank.Tensor.product P Q) (e + f) (Lemmata.TensorRank.Tensor.product S T) := by
  obtain ⟨E, hE⟩ := hP.exists_remainder
  obtain ⟨F, hF⟩ := hQ.exists_remainder
  apply Leading.of_remainder (fun x =>
    Polynomial.C (S (fun i => (x i).1)) * F (fun i => (x i).2) +
      E (fun i => (x i).1) * Polynomial.C (T (fun i => (x i).2)) +
      Polynomial.X * E (fun i => (x i).1) * F (fun i => (x i).2))
  intro x
  simp only [Lemmata.TensorRank.Tensor.product, hE, hF, map_mul, pow_add, pow_one]
  ring

theorem Leading.power {V : I → Type w}
    {P : Tensor (Polynomial R) I V} {T : Tensor R I V} {e : ℕ}
    (h : Leading P e T) (n : ℕ) :
    Leading (Lemmata.TensorRank.Tensor.power P n) (e * n) (Lemmata.TensorRank.Tensor.power T n) := by
  constructor
  · exact h.power_coefficient n
  · intro j hj
    funext x
    have hd (t : Fin n) : Polynomial.X ^ e ∣ P (fun i => x i t) :=
      Polynomial.X_pow_dvd_iff.mpr (fun d hd => congrFun (h.2 d hd) _)
    have hp : (∏ _t : Fin n, (Polynomial.X ^ e : Polynomial R)) ∣
        ∏ t : Fin n, P (fun i => x i t) :=
      Finset.prod_dvd_prod_of_dvd (fun _t : Fin n => (Polynomial.X ^ e : Polynomial R))
        (fun t => P (fun i => x i t)) (fun t _ => hd t)
    have hp' : Polynomial.X ^ (e * n) ∣ ∏ t : Fin n, P (fun i => x i t) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul] using hp
    exact Polynomial.X_pow_dvd_iff.mp hp' j hj

variable [Fintype I] {V : I → Type w} [∀ i, Fintype (V i)] {W : I → Type z}

theorem polynomialMap_substitution (A : ∀ i, W i → V i → Polynomial R)
    (T : Tensor R I V) (q : Polynomial R) :
    polynomialMap (fun i y x => (A i y x).comp q) T =
      fun y => (polynomialMap A T y).comp q := by
  funext y
  simp only [polynomialMap, localMap, Polynomial.sum_comp, Polynomial.mul_comp,
    Polynomial.prod_comp, Polynomial.C_comp]

theorem polynomialMap_product {U Z : I → Type*} [∀ i, Fintype (U i)]
    (A : ∀ i, W i → V i → Polynomial R) (B : ∀ i, Z i → U i → Polynomial R)
    (T : Tensor R I V) (S : Tensor R I U) :
    polynomialMap (productKernel A B) (Lemmata.TensorRank.Tensor.product T S) =
      Lemmata.TensorRank.Tensor.product (polynomialMap A T) (polynomialMap B S) := by
  have hc : (fun x => Polynomial.C (Lemmata.TensorRank.Tensor.product T S x)) =
      Lemmata.TensorRank.Tensor.product (fun x => Polynomial.C (T x)) (fun x => Polynomial.C (S x)) := by
    funext x
    simp only [Lemmata.TensorRank.Tensor.product, map_mul]
  unfold polynomialMap
  rw [hc, localMap_product]

theorem Degenerates.refl (T : Tensor R I V) : Degenerates T T := by
  refine ⟨fun _ y x => if x = y then 1 else 0, 0, ?_⟩
  change Leading (localMap (fun _ y x => if x = y then 1 else 0)
    (fun x => Polynomial.C (T x))) 0 T
  rw [localMap_select]
  constructor
  · funext x
    simp [coefficient, reindex]
  · intro j hj
    omega

theorem Degenerates.product {U Z : I → Type*} [∀ i, Fintype (U i)]
    {S : Tensor R I W} {T : Tensor R I V} {P : Tensor R I Z} {Q : Tensor R I U}
    (hS : Degenerates S T) (hP : Degenerates P Q) :
    Degenerates (Lemmata.TensorRank.Tensor.product S P) (Lemmata.TensorRank.Tensor.product T Q) := by
  obtain ⟨A, e, hA⟩ := hS
  obtain ⟨B, f, hB⟩ := hP
  refine ⟨productKernel A B, e + f, ?_⟩
  rw [polynomialMap_product]
  exact hA.product hB

theorem Degenerates.power {S : Tensor R I W} {T : Tensor R I V}
    (h : Degenerates S T) (n : ℕ) :
    Degenerates (Lemmata.TensorRank.Tensor.power S n) (Lemmata.TensorRank.Tensor.power T n) := by
  obtain ⟨A, e, hA⟩ := h
  refine ⟨powerKernel A n, e * n, ?_⟩
  rw [polynomialMap_power]
  exact hA.power n

theorem Degenerates.copies {S : Tensor R I W} {T : Tensor R I V}
    (h : Degenerates S T) (l : ℕ) : Degenerates (copies l S) (copies l T) :=
  (Degenerates.refl (diagonal (R := R) (I := I) l)).product h

variable [∀ i, Fintype (W i)]

theorem Degenerates.trans {U : I → Type*}
    {T : Tensor R I V} {S : Tensor R I W} {Q : Tensor R I U}
    (hQS : Degenerates Q S) (hST : Degenerates S T) : Degenerates Q T := by
  obtain ⟨A, e, hA⟩ := hST
  obtain ⟨B, f, hB⟩ := hQS
  obtain ⟨E, hE⟩ := hA.exists_remainder
  obtain ⟨F, hF⟩ := hB.exists_remainder
  let M := f + 1
  let A' : ∀ i, W i → V i → Polynomial R := fun i y x =>
    (A i y x).comp (Polynomial.X ^ M)
  let K : ∀ i, U i → V i → Polynomial R := fun i y x => ∑ w, B i y w * A' i w x
  let G : Tensor (Polynomial R) I W := fun y => (E y).comp (Polynomial.X ^ M)
  have hsubst : polynomialMap A' T = fun y =>
      Polynomial.X ^ (M * e) * Polynomial.C (S y) +
        Polynomial.X ^ (M * e + M) * G y := by
    rw [show A' = (fun i y x => (A i y x).comp (Polynomial.X ^ M)) from rfl,
      polynomialMap_substitution]
    funext y
    simp only [hE y, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_pow_comp,
      Polynomial.C_comp, ← pow_mul, Nat.mul_add, Nat.mul_one, G]
  have hcomposition : polynomialMap K T =
      fun y => Polynomial.X ^ (M * e) * polynomialMap B S y +
        Polynomial.X ^ (M * e + M) * localMap B G y := by
    have hc : polynomialMap K T = localMap B (polynomialMap A' T) := by
      unfold polynomialMap
      rw [localMap_comp]
    rw [hc, hsubst]
    change localMap B (((Polynomial.X : Polynomial R) ^ (M * e)) • (fun y => Polynomial.C (S y)) +
      ((Polynomial.X : Polynomial R) ^ (M * e + M)) • G) = _
    rw [localMap_add, localMap_smul, localMap_smul]
    rfl
  refine ⟨K, M * e + f, ?_⟩
  apply Leading.of_remainder (fun y => F y + localMap B G y)
  intro y
  rw [congrFun hcomposition y, hF y]
  dsimp only [M]
  simp only [pow_add, pow_one]
  ring

omit [∀ i, Fintype (W i)] in
theorem localMap_relabel_indices {J : Type*} [Fintype J] (e : J ≃ I)
    (A : ∀ i, W i → V i → R) (T : Tensor R I V) :
    localMap (fun j => A (e j)) (relabel e T) = relabel e (localMap A T) := by
  funext y
  unfold localMap relabel
  apply Fintype.sum_equiv (Equiv.piCongrLeft V e)
  intro x
  congr 1
  apply Fintype.prod_equiv e
  intro j
  simp

omit [∀ i, Fintype (W i)] in
theorem Degenerates.relabel_indices {J : Type*} [Fintype J] (e : J ≃ I)
    {S : Tensor R I W} {T : Tensor R I V} (h : Degenerates S T) :
    Degenerates (relabel e S) (relabel e T) := by
  obtain ⟨A, d, hA⟩ := h
  refine ⟨fun j => A (e j), d, ?_⟩
  have hc : (fun x => Polynomial.C (relabel e T x)) =
      relabel e (fun x => Polynomial.C (T x)) := rfl
  unfold polynomialMap
  rw [hc, localMap_relabel_indices]
  constructor
  · exact congrArg (fun Q : Tensor R I W => relabel e Q) hA.1
  · intro n hn
    exact congrArg (fun Q : Tensor R I W => relabel e Q) (hA.2 n hn)

end Lemmata.TensorRank.Tensor
