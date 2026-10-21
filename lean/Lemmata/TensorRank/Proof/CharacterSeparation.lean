module

public import Lemmata.TensorRank.Proof.CharacterProducts
public import Lemmata.TensorRank.Proof.TensorPermutation
public import Lemmata.TensorRank.Proof.ReaderTransport

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

variable {I J : Type} [Fintype I] [Fintype J] {V W : I → Type}

omit [Fintype I] [Fintype J] in
theorem relabel_reindex {R : Type*} (e : J ≃ I) (c : ∀ i, W i → V i)
    (T : Tensor R I V) :
    relabel e (reindex c T) = reindex (fun j => c (e j)) (relabel e T) := by
  funext x
  unfold relabel reindex
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [Equiv.piCongrLeft_apply_apply]

omit [Fintype I] [Fintype J] in
theorem relabel_inverse_reindex {R : Type*} (e : J ≃ I) (T : Tensor R I V) :
    reindex (fun i => Equiv.cast (congrArg V (e.apply_symm_apply i).symm))
      (relabel e.symm (relabel e T)) = T := by
  funext x
  unfold reindex relabel
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [Equiv.piCongrLeft_apply_apply]
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

omit [Fintype I] [Fintype J] in
theorem relabel_diagonal {R : Type*} [Zero R] [One R] (e : J ≃ I) (l : ℕ) :
    relabel e (diagonal (R := R) (I := I) l) = diagonal (I := J) l := by
  funext x
  simp only [relabel, diagonal]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j => by simpa only [Equiv.piCongrLeft_apply_apply] using ha (e j)⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    simpa only [Equiv.piCongrLeft_apply_apply] using ha j

omit [Fintype I] [Fintype J] in
theorem relabel_copies {R : Type*} [MulZeroOneClass R] (e : J ≃ I) (l : ℕ)
    (T : Tensor R I V) : relabel e (copies l T) = copies l (relabel e T) := by
  rw [copies, relabel_product, relabel_diagonal]
  rfl

variable [∀ i, Fintype (V i)]

omit [Fintype I] [Fintype J] [∀ i, Fintype (V i)] in
theorem Leading.relabel (e : J ≃ I) {P : Tensor (Polynomial ℂ) I W} {S : Tensor ℂ I W}
    {d : ℕ} (h : Leading P d S) : Leading (Tensor.relabel e P) d (Tensor.relabel e S) := by
  constructor
  · exact congrArg (fun Q : Tensor ℂ I W => Tensor.relabel e Q) h.1
  · intro n hn
    exact congrArg (fun Q : Tensor ℂ I W => Tensor.relabel e Q) (h.2 n hn)

theorem polynomialMap_relabel (e : J ≃ I) (A : ∀ i, W i → V i → Polynomial ℂ)
    (T : Tensor ℂ I V) :
    polynomialMap (fun j => A (e j)) (relabel e T) = relabel e (polynomialMap A T) := by
  have hc : (fun x => Polynomial.C (relabel e T x)) =
      relabel e (fun x => Polynomial.C (T x)) := rfl
  unfold polynomialMap
  rw [hc, localMap_relabel]

theorem Degenerates.relabel (e : J ≃ I) {S : Tensor ℂ I W} {T : Tensor ℂ I V}
    (h : Degenerates S T) : Degenerates (relabel e S) (relabel e T) := by
  obtain ⟨A, d, h⟩ := h
  refine ⟨fun j => A (e j), d, ?_⟩
  rw [polynomialMap_relabel]
  exact h.relabel e

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.TensorSemiring.Character

variable {k : ℕ} [Nonempty (Fin k)] (f : Character k)
variable {I : Type} [Fintype I] (e : I ≃ Fin k)
variable {V W : I → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def evalOn (T : Tensor ℂ I V) : ℝ := f.eval (Tensor.relabel e.symm T)

omit [Fintype I] in
theorem evalOn_nonneg (T : Tensor ℂ I V) : 0 ≤ f.evalOn e T := f.eval_nonneg _

omit [Nonempty (Fin k)] [Fintype I] in
theorem evalOn_product (S : Tensor ℂ I V) (T : Tensor ℂ I W) :
    f.evalOn e (Tensor.product S T) = f.evalOn e S * f.evalOn e T := by
  rw [evalOn, Tensor.relabel_product, eval_product]
  rfl

omit [Nonempty (Fin k)] [Fintype I] in
theorem evalOn_power (T : Tensor ℂ I V) (n : ℕ) :
    f.evalOn e (Tensor.power T n) = f.evalOn e T ^ n := by
  rw [evalOn, Tensor.relabel_power, eval_power]
  rfl

omit [Fintype I] in
theorem evalOn_copies (l : ℕ) (T : Tensor ℂ I V) :
    f.evalOn e (Tensor.copies l T) = l * f.evalOn e T := by
  rw [evalOn, Tensor.relabel_copies, eval_copies]
  rfl

omit [Nonempty (Fin k)] [Fintype I] in
theorem evalOn_reindex (c : ∀ i, W i ≃ V i) (T : Tensor ℂ I V) :
    f.evalOn e (Tensor.reindex (fun i => c i) T) = f.evalOn e T := by
  rw [evalOn, Tensor.relabel_reindex, eval_reindex]
  rfl

omit [Nonempty (Fin k)] in
theorem evalOn_monotone {S : Tensor ℂ I W} {T : Tensor ℂ I V} (h : Tensor.Restricts S T) :
    f.evalOn e S ≤ f.evalOn e T := f.monotone (h.relabel e.symm)

theorem evalOn_degenerates {S : Tensor ℂ I W} {T : Tensor ℂ I V} (h : Tensor.Degenerates S T) :
    f.evalOn e S ≤ f.evalOn e T := f.eval_degenerates (h.relabel e.symm)

omit [Nonempty (Fin k)] [Fintype I] in
theorem evalOn_relabel {U : Fin k → Type} [∀ i, Fintype (U i)]
    (T : Tensor ℂ (Fin k) U) : f.evalOn e (Tensor.relabel e T) = f.eval T := by
  rw [evalOn, ← eval_reindex f (fun i => Equiv.cast (congrArg U (e.apply_symm_apply i).symm)),
    Tensor.relabel_inverse_reindex]

omit [Nonempty (Fin k)] [Fintype I] in
theorem evalOn_context {U : Fin k → Type} [∀ i, Fintype (U i)]
    (S : Tensor ℂ I V) (T : Tensor ℂ (Fin k) U) :
    f.evalOn e (Tensor.product S (Tensor.relabel e T)) =
      f.eval (Tensor.product (Tensor.relabel e.symm S) T) := by
  rw [← Tensor.relabel_context_reindex e S T, evalOn_reindex]
  exact f.evalOn_relabel e (Tensor.product (Tensor.relabel e.symm S) T)

end Lemmata.TensorRank.TensorSemiring.Character

namespace Lemmata.TensorRank.Separation

variable {k r M : ℕ} [Nonempty (Fin k)] (f : TensorSemiring.Character k)
variable (e : Party r ≃ Fin k) {V W : Party r → Type}
variable [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]

theorem character_equal_sectors_bound (hM : 0 < M) (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hl : Tensor.Reads Z (.inl false) left) (hr : Tensor.Reads Z (.inl true) right)
    (T : Tensor ℂ (Party r) W) (c : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (hc : ∀ q, Tensor.reindex (fun p => c q p) T = Z q) :
    f.evalOn e (Tensor.product (readerPairing M) T) ≤
      ((r + 1 : ℕ) : ℝ) * f.evalOn e (∑ q, Z q) := by
  have hd := f.evalOn_degenerates e (separated_degenerates_sum hM Z hl hr)
  rw [← equal_sectors_reindex Z T c hc, f.evalOn_reindex, f.evalOn_copies,
    f.evalOn_copies] at hd
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mp
  convert hd using 1
  simp only [period, Nat.cast_mul]
  ring

theorem character_fixed_type_bound {C : Type} [Fintype C] {N : ℕ}
    (Z : C → Tensor ℂ (Party r) V)
    {left : V (.inl false) → C} {right : V (.inl true) → C}
    (hl : Tensor.Reads Z (.inl false) left) (hr : Tensor.Reads Z (.inl true) right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    f.evalOn e (Tensor.product (readerPairing (Fintype.card (Types.Words h)))
      (Tensor.wordTensor Z base.val)) ≤
      ((r + 1 : ℕ) : ℝ) * f.evalOn e (∑ c, Z c) ^ N := by
  have hM : 0 < Fintype.card (Types.Words h) := Fintype.card_pos_iff.mpr ⟨base⟩
  have hb := character_equal_sectors_bound f e hM (typedFamily Z h)
    (typedFamily_reads Z hl base) (typedFamily_reads Z hr base)
    (Tensor.wordTensor Z base.val)
    (fun q p => Tensor.wordCoordinate
      (((Fintype.equivFin (Types.Words h)).symm q).property.trans base.property.symm) p)
    (typedFamily_reindex Z base)
  rw [typedFamily_sum] at hb
  apply hb.trans
  have ht := f.evalOn_monotone e (Tensor.typeSector_restricts_power Z hl h)
  rw [f.evalOn_power] at ht
  exact mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)

theorem character_fixed_type_bound_readers (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    {C : Type} [Fintype C] {N : ℕ} {U : Fin k → Type} [∀ i, Fintype (U i)]
    (Z : C → Tensor ℂ (Fin k) U) {left : U a → C} {right : U b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    f.eval (Tensor.product
      (Tensor.relabel (readerEquiv a b hab).symm (readerPairing (Fintype.card (Types.Words h))))
      (Tensor.wordTensor Z base.val)) ≤ ((k - 1 : ℕ) : ℝ) * f.eval (∑ c, Z c) ^ N := by
  let e := readerEquiv a b hab
  have hleft : Tensor.Reads (fun c => Tensor.relabel e (Z c)) (.inl false) left :=
    Tensor.Reads.relabel e (.inl false) hl
  have hright : Tensor.Reads (fun c => Tensor.relabel e (Z c)) (.inl true) right :=
    Tensor.Reads.relabel e (.inl true) hr
  have hb := character_fixed_type_bound f e (fun c => Tensor.relabel e (Z c)) hleft hright base
  rw [← Tensor.relabel_sum, f.evalOn_relabel, ← Tensor.relabel_wordTensor,
    f.evalOn_context] at hb
  simpa only [show k - 2 + 1 = k - 1 by omega] using hb

omit [Nonempty (Fin k)] in
theorem character_readerPairing_eq (a b : Fin k) (hab : a ≠ b) (M : ℕ) :
    f.eval (Tensor.relabel (readerEquiv a b hab).symm (readerPairing M)) =
      f.eval (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M)) := by
  change f.evalOn (readerEquiv a b hab) (readerPairing M) = _
  rw [← pairingGraph_reindex a b hab M, f.evalOn_reindex]
  exact f.evalOn_relabel (readerEquiv a b hab)
    (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M))

theorem character_fixed_type_edge_bound (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    {C : Type} [Fintype C] {N : ℕ} {U : Fin k → Type} [∀ i, Fintype (U i)]
    (Z : C → Tensor ℂ (Fin k) U) {left : U a → C} {right : U b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    f.eval (weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm)
      (Fintype.card (Types.Words h)))) * (∏ c, f.eval (Z c) ^ (h c).val) ≤
        ((k - 1 : ℕ) : ℝ) * f.eval (∑ c, Z c) ^ N := by
  have hb := character_fixed_type_bound_readers f hk a b hab Z hl hr base
  rw [f.eval_product, character_readerPairing_eq f a b hab, f.eval_wordTensor,
    base.property] at hb
  exact hb

end Lemmata.TensorRank.Separation
