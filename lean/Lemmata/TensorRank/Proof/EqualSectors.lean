module

public import Lemmata.TensorRank.Proof.WordSectors

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.Tensor

theorem Reads.product_right {R I C : Type*} [CommSemiring R] {V U : I → Type*}
    {Z : C → Tensor R I V} {reader : I} {label : V reader → C}
    (h : Reads Z reader label) (H : Tensor R I U) :
    Reads (fun q => product (Z q) H) reader (fun x => label x.1) := by
  intro q x hx
  apply h q (fun i => (x i).1)
  intro hz
  apply hx
  change Z q (fun i => (x i).1) * H (fun i => (x i).2) = 0
  rw [hz, zero_mul]

theorem sum_product_right {R I C : Type*} [CommSemiring R] [Fintype C]
    {V U : I → Type*} (Z : C → Tensor R I V) (H : Tensor R I U) :
    (∑ q, product (Z q) H) = product (∑ q, Z q) H := by
  funext x
  simp only [product, Finset.sum_apply, Finset.sum_mul]

end Lemmata.TensorRank.Tensor

namespace Lemmata.TensorRank.Separation

universe u v w

abbrev PairCoordinate {r : ℕ} (M : ℕ) : Party r → Type
  | .inl _ => Fin M
  | .inr _ => PUnit

instance {r M : ℕ} (p : Party r) : Fintype (PairCoordinate M p) := by
  cases p <;> infer_instance

def readerPairing {r : ℕ} (M : ℕ) : Tensor ℂ (Party r) (PairCoordinate M) :=
  fun x => if x (.inl false) = x (.inl true) then 1 else 0

variable {r M : ℕ} {V : Party r → Type u} {W : Party r → Type v}

def equalCoordinate (e : ∀ _ : Fin M, ∀ p, V p ≃ W p) (p : Party r) :
    SeparatedCoordinate V M p ≃ (Fin M × (PairCoordinate M p × W p)) :=
  match p with
  | .inl b =>
    { toFun := fun x => (x.1.1, (x.1.2, e x.1.1 (.inl b) x.2))
      invFun := fun x => ((x.1, x.2.1), (e x.1 (.inl b)).symm x.2.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  | .inr i =>
    { toFun := fun x => (x.1, (PUnit.unit, e x.1 (.inr i) x.2))
      invFun := fun x => (x.1, (e x.1 (.inr i)).symm x.2.2)
      left_inv := fun x => by simp
      right_inv := fun x => by cases x.2.1; simp }

theorem equalCoordinate_label (e : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (p : Party r) (x : SeparatedCoordinate V M p) :
    (equalCoordinate e p x).1 = label p x := by cases p <;> rfl

theorem equalCoordinate_input (e : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (p : Party r) (x : SeparatedCoordinate V M p) :
    (equalCoordinate e p x).2.2 = e (label p x) p x.2 := by cases p <;> rfl

theorem equal_sectors_reindex (Z : Fin M → Tensor ℂ (Party r) V)
    (T : Tensor ℂ (Party r) W) (e : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (he : ∀ h, Tensor.reindex (fun p => e h p) T = Z h) :
    Tensor.reindex (fun p => equalCoordinate e p)
      (Tensor.copies M (Tensor.product (readerPairing M) T)) = separatedSum Z := by
  funext x
  simp only [Tensor.reindex, Tensor.copies, Tensor.product, Tensor.diagonal,
    equalCoordinate_label, equalCoordinate_input, readerPairing]
  change (if ∃ h : Fin M, ∀ p, label p (x p) = h then 1 else 0) *
    ((if (x (.inl false)).1.2 = (x (.inl true)).1.2 then 1 else 0) *
      T (fun p => e (label p (x p)) p (x p).2)) = _
  have hc : (∃ h : Fin M, ∀ p, label p (x p) = h) ↔
      ∀ p, label p (x p) = (x (.inl false)).1.1 := by
    constructor
    · rintro ⟨h, hh⟩ p
      exact (hh p).trans (hh (.inl false)).symm
    · intro hh
      exact ⟨(x (.inl false)).1.1, hh⟩
  simp only [hc]
  by_cases hl : ∀ p, label p (x p) = (x (.inl false)).1.1
  · have ht : T (fun p => e (label p (x p)) p (x p).2) =
        Z (x (.inl false)).1.1 (fun p => (x p).2) := by
      simpa only [Tensor.reindex, hl] using congrFun (he (x (.inl false)).1.1) (fun p => (x p).2)
    rw [ite_eq_left hl, one_mul, ht]
    by_cases hp : (x (.inl false)).1.2 = (x (.inl true)).1.2
    · rw [ite_eq_left hp]
      simp only [one_mul, separatedSum]
      exact (ite_eq_left ⟨hl, hp⟩).symm
    · rw [ite_eq_right hp]
      simp only [zero_mul, separatedSum]
      symm
      apply ite_eq_right
      intro h
      exact hp h.2
  · rw [ite_eq_right hl]
    simp only [zero_mul, separatedSum]
    symm
    apply ite_eq_right
    intro h
    exact hl h.1

theorem asymptoticRank_separated_eq [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    (hM : 0 < M) (Z : Fin M → Tensor ℂ (Party r) V)
    (T : Tensor ℂ (Party r) W) (e : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (he : ∀ h, Tensor.reindex (fun p => e h p) T = Z h) :
    Tensor.asymptoticRank (separatedSum Z) =
      (M : ℝ) * Tensor.asymptoticRank (Tensor.product (readerPairing M) T) := by
  rw [← equal_sectors_reindex Z T e he, Tensor.asymptoticRank_reindex]
  exact Tensor.asymptoticRank_copies M hM _ (.inl false) (.inl true) (by simp)

theorem equal_sectors_bound [∀ p, Fintype (V p)] [∀ p, Fintype (W p)]
    (hM : 0 < M) (Z : Fin M → Tensor ℂ (Party r) V)
    {left : V (.inl false) → Fin M} {right : V (.inl true) → Fin M}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right)
    (T : Tensor ℂ (Party r) W) (e : ∀ _ : Fin M, ∀ p, V p ≃ W p)
    (he : ∀ h, Tensor.reindex (fun p => e h p) T = Z h) :
    Tensor.asymptoticRank (Tensor.product (readerPairing M) T) ≤
      ((r + 1 : ℕ) : ℝ) * Tensor.asymptoticRank (∑ q, Z q) := by
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mp
  calc
    (M : ℝ) * Tensor.asymptoticRank (Tensor.product (readerPairing M) T) =
        Tensor.asymptoticRank (separatedSum Z) := (asymptoticRank_separated_eq hM Z T e he).symm
    _ ≤ (period r M : ℝ) * Tensor.asymptoticRank (∑ q, Z q) :=
      separated_asymptoticRank_sum_le hM Z hleft hright
    _ = _ := by simp only [period, Nat.cast_mul]; ring

variable {C : Type*} [Fintype C] {N : ℕ}

def typedWordIndex {h : C → Fin (N + 1)} (base : Types.Words h) (w : Fin N → C) :
    Fin (Fintype.card (Types.Words h)) :=
  if hw : Types.histogram w = h then Fintype.equivFin (Types.Words h) ⟨w, hw⟩
  else Fintype.equivFin (Types.Words h) base

theorem typedWordIndex_decode {h : C → Fin (N + 1)} (base : Types.Words h)
    (q : Fin (Fintype.card (Types.Words h))) :
    typedWordIndex base ((Fintype.equivFin (Types.Words h)).symm q).val = q := by
  simp only [typedWordIndex,
    dite_eq_left ((Fintype.equivFin (Types.Words h)).symm q).property]
  exact (Fintype.equivFin (Types.Words h)).apply_symm_apply q

def typedFamily (Z : C → Tensor ℂ (Party r) V) (h : C → Fin (N + 1))
    (q : Fin (Fintype.card (Types.Words h))) :
    Tensor ℂ (Party r) (fun p => Fin N → V p) :=
  Tensor.wordTensor Z ((Fintype.equivFin (Types.Words h)).symm q).val

theorem typedFamily_sum (Z : C → Tensor ℂ (Party r) V) (h : C → Fin (N + 1)) :
    (∑ q, typedFamily Z h q) = Tensor.typeSector Z h :=
  Equiv.sum_comp (Fintype.equivFin (Types.Words h)).symm (fun w => Tensor.wordTensor Z w.val)

theorem typedFamily_reads (Z : C → Tensor ℂ (Party r) V)
    {reader : Party r} {label : V reader → C} (hr : Tensor.Reads Z reader label)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    Tensor.Reads (typedFamily Z h) reader (fun y => typedWordIndex base (fun j => label (y j))) := by
  intro q x hx
  have hw := hr.wordTensor N ((Fintype.equivFin (Types.Words h)).symm q).val x hx
  change (fun j => label (x reader j)) = ((Fintype.equivFin (Types.Words h)).symm q).val at hw
  change typedWordIndex base (fun j => label (x reader j)) = q
  rw [hw]
  exact typedWordIndex_decode base q

theorem typedFamily_reindex (Z : C → Tensor ℂ (Party r) V)
    {h : C → Fin (N + 1)} (base : Types.Words h)
    (q : Fin (Fintype.card (Types.Words h))) :
    Tensor.reindex (fun p => Tensor.wordCoordinate
      (((Fintype.equivFin (Types.Words h)).symm q).property.trans base.property.symm) p)
      (Tensor.wordTensor Z base.val) = typedFamily Z h q :=
  Tensor.wordTensor_reindex Z _

theorem fixed_type_bound [∀ p, Fintype (V p)] (Z : C → Tensor ℂ (Party r) V)
    {left : V (.inl false) → C} {right : V (.inl true) → C}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    Tensor.asymptoticRank (Tensor.product (readerPairing (Fintype.card (Types.Words h)))
      (Tensor.wordTensor Z base.val)) ≤
      ((r + 1 : ℕ) : ℝ) * Tensor.asymptoticRank (∑ c, Z c) ^ N := by
  have hM : 0 < Fintype.card (Types.Words h) := Fintype.card_pos_iff.mpr ⟨base⟩
  have hb := equal_sectors_bound hM (typedFamily Z h)
    (typedFamily_reads Z hleft base) (typedFamily_reads Z hright base)
    (Tensor.wordTensor Z base.val)
    (fun q p => Tensor.wordCoordinate
      (((Fintype.equivFin (Types.Words h)).symm q).property.trans base.property.symm) p)
    (typedFamily_reindex Z base)
  rw [typedFamily_sum] at hb
  apply hb.trans
  have hr := (Tensor.typeSector_restricts_power Z hleft h).asymptoticRank_le
  rw [Tensor.asymptoticRank_power] at hr
  exact mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)

theorem fixed_type_bound_context {U : Party r → Type w}
    [∀ p, Fintype (V p)] [∀ p, Fintype (U p)]
    (Z : C → Tensor ℂ (Party r) V) (H : Tensor ℂ (Party r) U)
    {left : V (.inl false) → C} {right : V (.inl true) → C}
    (hleft : Tensor.Reads Z (.inl false) left) (hright : Tensor.Reads Z (.inl true) right)
    {h : C → Fin (N + 1)} (base : Types.Words h) :
    Tensor.asymptoticRank (Tensor.product (readerPairing (Fintype.card (Types.Words h)))
      (Tensor.product (Tensor.wordTensor Z base.val) H)) ≤
      ((r + 1 : ℕ) : ℝ) *
        Tensor.asymptoticRank (Tensor.product (Tensor.power (∑ c, Z c) N) H) := by
  let F := fun q => Tensor.product (typedFamily Z h q) H
  let e (q : Fin (Fintype.card (Types.Words h))) (p : Party r) :
      ((Fin N → V p) × U p) ≃ ((Fin N → V p) × U p) :=
    Equiv.prodCongr (Tensor.wordCoordinate (V := V)
      (((Fintype.equivFin (Types.Words h)).symm q).property.trans base.property.symm) p)
      (Equiv.refl (U p))
  have he (q : Fin (Fintype.card (Types.Words h))) :
      Tensor.reindex (fun p => e q p) (Tensor.product (Tensor.wordTensor Z base.val) H) = F q := by
    funext x
    exact congrArg (fun t => t * H (fun p => (x p).2))
      (congrFun (typedFamily_reindex Z base q) (fun p => (x p).1))
  have hs : (∑ q, F q) = Tensor.product (Tensor.typeSector Z h) H := by
    dsimp [F]
    rw [Tensor.sum_product_right, typedFamily_sum]
  have hM : 0 < Fintype.card (Types.Words h) := Fintype.card_pos_iff.mpr ⟨base⟩
  have hb := equal_sectors_bound hM F
    ((typedFamily_reads Z hleft base).product_right H)
    ((typedFamily_reads Z hright base).product_right H)
    (Tensor.product (Tensor.wordTensor Z base.val) H) e he
  rw [hs] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (((Tensor.typeSector_restricts_power Z hleft h).product (Tensor.Restricts.refl H)).asymptoticRank_le)
    (Nat.cast_nonneg _)

end Lemmata.TensorRank.Separation
