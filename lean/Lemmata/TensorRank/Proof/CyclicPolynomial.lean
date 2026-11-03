module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.CyclicPolynomial
public import Lemmata.TensorRank.Proof.CyclicSchedule
public import Lemmata.TensorRank.Proof.PolynomialInputReindex
public import Lemmata.TensorRank.Proof.PairedShortening

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.CyclicPolynomial

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} [NeZero k]

open PolynomialProduct

private theorem context_relabel_left {I : Type} [Fintype I]
    {V : I → Type} [∀ i, Fintype (V i)] {W : Fin k → Type} [∀ i, Fintype (W i)]
    (e f : Fin k ≃ I) (hef : e = f) (S : Tensor 𝕜 I V) (T : Tensor 𝕜 (Fin k) W) :
    Tensor.ContextLE 1 (Tensor.relabel e S) T ↔ Tensor.ContextLE 1 (Tensor.relabel f S) T := by
  subst f
  rfl

private theorem context_relabel_right {I : Type} [Fintype I]
    {V : I → Type} [∀ i, Fintype (V i)] {W : Fin k → Type} [∀ i, Fintype (W i)]
    (e f : Fin k ≃ I) (hef : e = f) (S : Tensor 𝕜 (Fin k) W) (T : Tensor 𝕜 I V) :
    Tensor.ContextLE 1 S (Tensor.relabel e T) ↔ Tensor.ContextLE 1 S (Tensor.relabel f T) := by
  subst f
  rfl

private theorem placed_context_of_eq (e : Fin k ≃ ZMod k) (j : ZMod k)
    (a b : Input j → ℕ) (hab : a = b) :
    Tensor.ContextLE 1 (placed (𝕜 := 𝕜) (outputParties e j) a)
      (placed (𝕜 := 𝕜) (outputParties e j) b) := by
  subst b
  exact Tensor.ContextLE.refl _

theorem tensor_context_of_input_eq (e : Fin k ≃ ZMod k) (j : ZMod k)
    (a b : ZMod k → ℕ) (hab : ∀ p : Input j, a p.val = b p.val) :
    Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e j a) (tensor (𝕜 := 𝕜) e j b) :=
  placed_context_of_eq e j _ _ (funext hab)

theorem input_card (j : ZMod k) : Fintype.card (Input j) = k - 1 := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe j)
  simp only [Fintype.card_option, ZMod.card] at h
  have hc : Fintype.card (Input j) + 1 = k := by
    convert h using 1
  omega

theorem constant_degree (j : ZMod k) (n : ℕ) :
    degree (fun _ : Input j => n) = (k - 1) * (n - 1) := by
  simp [degree, input_card]

theorem tensor_asymptoticRank_le (e : Fin k ≃ ZMod k) (j : ZMod k) (a : ZMod k → ℕ) :
    Tensor.asymptoticRank (tensor (𝕜 := 𝕜) e j a) ≤
      ((degree (fun p : Input j => a p.val) + 1 : ℕ) : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, NeZero.pos k⟩⟩
  have h := ((tensor_degenerates_diagonal (𝕜 := 𝕜) (fun p : Input j => a p.val)).relabel_indices
    (outputParties e j)).asymptoticRank_le
  apply h.trans
  apply (Tensor.asymptoticRank_le_rank _).trans
  have hr : Tensor.rank (Tensor.relabel (outputParties e j)
      (Tensor.diagonal (R := 𝕜) (I := Option (Input j))
        (degree (fun p : Input j => a p.val) + 1))) ≤
      degree (fun p : Input j => a p.val) + 1 := by
    calc
      _ = Tensor.rank (Tensor.diagonal (R := 𝕜) (I := Option (Input j))
          (degree (fun p : Input j => a p.val) + 1)) :=
        Tensor.rank_relabel (outputParties e j)
          (Tensor.diagonal (R := 𝕜) (I := Option (Input j))
            (degree (fun p : Input j => a p.val) + 1))
      _ ≤ _ := Tensor.rank_diagonal_le _
  exact_mod_cast hr

theorem tensor_constant_asymptoticRank_le (e : Fin k ≃ ZMod k) (j : ZMod k) (n : ℕ) :
    Tensor.asymptoticRank (tensor (𝕜 := 𝕜) e j (fun _ => n)) ≤
      ((1 + (k - 1) * (n - 1) : ℕ) : ℝ) := by
  simpa only [constant_degree, Nat.add_comm] using
    tensor_asymptoticRank_le (𝕜 := 𝕜) e j (fun _ => n)

theorem tensor_ne_zero (e : Fin k ≃ ZMod k) (j : ZMod k) (a : ZMod k → ℕ)
    (ha : ∀ p, 0 < a p) : tensor (𝕜 := 𝕜) e j a ≠ 0 := by
  intro hz
  apply PolynomialProduct.tensor_ne_zero (𝕜 := 𝕜) (fun p : Input j => a p.val)
    (fun p => ha p.val)
  funext x
  have hx := congrFun hz
    ((Equiv.piCongrLeft (PolynomialProduct.Coordinate (fun p : Input j => a p.val))
      (outputParties e j)).symm x)
  simpa only [tensor, placed, Tensor.relabel, Equiv.apply_symm_apply, Pi.zero_apply] using hx

theorem tensor_one_rank (e : Fin k ≃ ZMod k) (j : ZMod k) :
    Tensor.rank (tensor (𝕜 := 𝕜) e j (fun _ => 1)) = 1 := by
  have he : PolynomialProduct.tensor (𝕜 := 𝕜) (fun _ : Input j => 1) =
      Tensor.pure (fun _ _ => (1 : 𝕜)) := by
    funext x
    have hs : (∑ p : Input j, (x (some p)).val) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have := (x (some p)).isLt
      change (x (some p)).val < 1 at this
      omega
    have hz : (x none).val = 0 := by
      have := (x none).isLt
      simp only [Coordinate, degree, Nat.sub_self, Finset.sum_const_zero, zero_add] at this
      omega
    simp only [PolynomialProduct.tensor, hs, hz, if_true, Tensor.pure, Finset.prod_const_one]
  have hu : Tensor.rank (tensor (𝕜 := 𝕜) e j (fun _ => 1)) ≤ 1 := by
    change Tensor.rank (Tensor.relabel (outputParties e j)
      (PolynomialProduct.tensor (𝕜 := 𝕜) (fun _ : Input j => 1))) ≤ 1
    rw [he, Tensor.relabel_pure]
    exact Tensor.rank_pure_le _
  apply Nat.le_antisymm hu
  apply Nat.one_le_iff_ne_zero.mpr
  intro hz
  exact tensor_ne_zero (𝕜 := 𝕜) e j (fun _ => 1) (fun _ => by decide)
    ((Tensor.rank_eq_zero_iff _).mp hz)

theorem stageFactor_zero_asymptoticRank_le (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.asymptoticRank (stageFactor (𝕜 := 𝕜) e b 0 t) ≤
      ((1 + (k - 1) * b : ℕ) : ℝ) := by
  have hc : Tensor.ContextLE 1 (stageFactor (𝕜 := 𝕜) e b 0 t)
      (tensor (𝕜 := 𝕜) e t.1 (fun _ => b + 1)) :=
    tensor_context_of_input_eq e t.1 _ _ (fun p => CyclicSchedule.inputLength_zero b t p.val)
  calc
    _ ≤ Tensor.asymptoticRank (tensor (𝕜 := 𝕜) e t.1 (fun _ => b + 1)) := by
      simpa only [one_mul] using hc.asymptoticRank_le
    _ ≤ _ := by
      simpa only [Nat.add_sub_cancel] using
        tensor_constant_asymptoticRank_le (𝕜 := 𝕜) e t.1 (b + 1)

theorem stageFactor_full_asymptoticRank_le (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.asymptoticRank (stageFactor (𝕜 := 𝕜) e b (k - 1) t) ≤
      ((1 + (k - 1) * (b - 1) : ℕ) : ℝ) := by
  have ha : (fun p : Input t.1 => CyclicSchedule.inputLength b (k - 1) t p.val) =
      (fun _ => b) := by
    funext p
    exact CyclicSchedule.inputLength_full b t p.val p.property
  change Tensor.asymptoticRank (placed (𝕜 := 𝕜) (outputParties e t.1)
    (fun p : Input t.1 => CyclicSchedule.inputLength b (k - 1) t p.val)) ≤ _
  rw [ha]
  exact tensor_constant_asymptoticRank_le (𝕜 := 𝕜) e t.1 b

theorem stageFactor_full_one_rank (e : Fin k ≃ ZMod k) (t : CyclicSchedule.Token k) :
    Tensor.rank (stageFactor (𝕜 := 𝕜) e 1 (k - 1) t) = 1 := by
  have ha : (fun p : Input t.1 => CyclicSchedule.inputLength 1 (k - 1) t p.val) =
      (fun _ => 1) := by
    funext p
    exact CyclicSchedule.inputLength_full 1 t p.val p.property
  change Tensor.rank (placed (𝕜 := 𝕜) (outputParties e t.1)
    (fun p : Input t.1 => CyclicSchedule.inputLength 1 (k - 1) t p.val)) = 1
  rw [ha]
  exact tensor_one_rank (𝕜 := 𝕜) e t.1

theorem stageFactor_zero_context_constant (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.ContextLE 1 (stageFactor (𝕜 := 𝕜) e b 0 t)
      (tensor (𝕜 := 𝕜) e t.1 (fun _ => b + 1)) :=
  tensor_context_of_input_eq e t.1 _ _ (fun p => CyclicSchedule.inputLength_zero b t p.val)

theorem constant_context_stageFactor_zero (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e t.1 (fun _ => b + 1))
      (stageFactor (𝕜 := 𝕜) e b 0 t) :=
  tensor_context_of_input_eq e t.1 _ _ (fun p => (CyclicSchedule.inputLength_zero b t p.val).symm)

theorem stageFactor_full_context_constant (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.ContextLE 1 (stageFactor (𝕜 := 𝕜) e b (k - 1) t)
      (tensor (𝕜 := 𝕜) e t.1 (fun _ => b)) :=
  tensor_context_of_input_eq e t.1 _ _
    (fun p => CyclicSchedule.inputLength_full b t p.val p.property)

theorem constant_context_stageFactor_full (e : Fin k ≃ ZMod k) (b : ℕ)
    (t : CyclicSchedule.Token k) :
    Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e t.1 (fun _ => b))
      (stageFactor (𝕜 := 𝕜) e b (k - 1) t) :=
  tensor_context_of_input_eq e t.1 _ _
    (fun p => (CyclicSchedule.inputLength_full b t p.val p.property).symm)

def sharedInputEquiv (a z : ZMod k) (h : a ≠ z) :
    CyclicSchedule.Shared a z ≃ Other (⟨a, h⟩ : Input z) where
  toFun p := ⟨⟨p.val, p.property.2⟩, by
    intro he
    exact p.property.1 (congrArg Subtype.val he)⟩
  invFun p := ⟨p.val.val, by
    constructor
    · intro he
      exact p.property (Subtype.ext he)
    · exact p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def dualSharedInputEquiv (a z : ZMod k) (h : a ≠ z) :
    CyclicSchedule.Shared a z ≃ Other (⟨z, h.symm⟩ : Input a) where
  toFun p := ⟨⟨p.val, p.property.1⟩, by
    intro he
    exact p.property.2 (congrArg Subtype.val he)⟩
  invFun p := ⟨p.val.val, by
    constructor
    · exact p.val.property
    · intro he
      exact p.property (Subtype.ext he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem readerParties_selected (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z) :
    (readerParties e a z h).trans
      (Equiv.sumCongr (Equiv.refl Bool) (sharedInputEquiv a z h)) =
        selectedParties (outputParties e z) (⟨a, h⟩ : Input z) := by
  apply Equiv.ext
  intro i
  apply (inputPartyEquiv (⟨a, h⟩ : Input z)).injective
  by_cases ha : e i = a
  · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, selectedParties,
      outputParties, Equiv.optionSubtypeNe_symm_of_ne h]
  · by_cases hz : e i = z
    · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, hz, h.symm,
        selectedParties, outputParties]
    · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, hz,
        selectedParties, outputParties, sharedInputEquiv,
        Equiv.optionSubtypeNe_symm_of_ne hz]

theorem readerParties_dual_selected (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z) :
    ((readerParties e a z h).trans Packing.swapReaders).trans
      (Equiv.sumCongr (Equiv.refl Bool) (dualSharedInputEquiv a z h)) =
        selectedParties (outputParties e a) (⟨z, h.symm⟩ : Input a) := by
  apply Equiv.ext
  intro i
  apply (inputPartyEquiv (⟨z, h.symm⟩ : Input a)).injective
  by_cases ha : e i = a
  · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, selectedParties,
      outputParties, Packing.swapReaders]
  · by_cases hz : e i = z
    · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, hz, h.symm, selectedParties,
        outputParties, Packing.swapReaders, Equiv.optionSubtypeNe_symm_of_ne h.symm]
    · simp [readerParties, CyclicSchedule.readerPartiesEquiv, ha, hz, selectedParties,
        outputParties, Packing.swapReaders, dualSharedInputEquiv,
        Equiv.optionSubtypeNe_symm_of_ne ha]

theorem tensor_context_selected {J : Type} [Fintype J]
    (e : Fin k ≃ ZMod k) (j : ZMod k) (a : ZMod k → ℕ) (r : Input j)
    (hr : 0 < a r.val) (s : J ≃ Other r) (R : Fin k ≃ (Bool ⊕ J))
    (hR : R.trans (Equiv.sumCongr (Equiv.refl Bool) s) =
      selectedParties (outputParties e j) r) :
    Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e j a)
      (Tensor.relabel R (selected (𝕜 := 𝕜)
        (remaining (fun p : Input j => a p.val) r ∘ s) (a r.val))) := by
  let : Fintype (Other r) := @Subtype.fintype (Input j) (fun i => i ≠ r)
    (fun i => @instDecidableNot (i = r) (Classical.propDecidable (i = r)))
    (inferInstance : Fintype (Input j))
  have hp := placed_context_selected (𝕜 := 𝕜) (outputParties e j)
    (fun p : Input j => a p.val) r hr
  have ht := (relabel_inputs_context_selected (𝕜 := 𝕜) s
    (remaining (fun p : Input j => a p.val) r) (a r.val)).relabel R
  rw [Tensor.relabel_comp_indices] at ht
  have ht' := (context_relabel_left _ _ hR _ _).mp ht
  simpa only [one_mul, tensor] using hp.trans ht' zero_le_one

theorem selected_context_tensor {J : Type} [Fintype J]
    (e : Fin k ≃ ZMod k) (j : ZMod k) (a : ZMod k → ℕ) (r : Input j)
    (hr : 0 < a r.val) (s : J ≃ Other r) (R : Fin k ≃ (Bool ⊕ J))
    (hR : R.trans (Equiv.sumCongr (Equiv.refl Bool) s) =
      selectedParties (outputParties e j) r) :
    Tensor.ContextLE 1
      (Tensor.relabel R (selected (𝕜 := 𝕜)
        (remaining (fun p : Input j => a p.val) r ∘ s) (a r.val)))
      (tensor (𝕜 := 𝕜) e j a) := by
  let : Fintype (Other r) := @Subtype.fintype (Input j) (fun i => i ≠ r)
    (fun i => @instDecidableNot (i = r) (Classical.propDecidable (i = r)))
    (inferInstance : Fintype (Input j))
  have hp := selected_context_placed (𝕜 := 𝕜) (outputParties e j)
    (fun p : Input j => a p.val) r hr
  have ht := (selected_context_relabel_inputs (𝕜 := 𝕜) s
    (remaining (fun p : Input j => a p.val) r) (a r.val)).relabel R
  rw [Tensor.relabel_comp_indices] at ht
  have ht' := (context_relabel_right _ _ hR _ _).mp ht
  simpa only [one_mul, tensor] using ht'.trans hp zero_le_one

private theorem pair_contexts (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z)
    (A B : ZMod k → ℕ) (b : ℕ) (hb : 0 < b)
    (hAz : A z = b) (hBa : B a = b)
    (hshared : ∀ p : CyclicSchedule.Shared a z, A p.val = B p.val) :
    Tensor.ContextLE 1
      (Tensor.product (tensor (𝕜 := 𝕜) e a A) (tensor (𝕜 := 𝕜) e z B))
      (Tensor.relabel (readerParties e a z h)
        (Packing.Paired.short (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => A p.val) b)) ∧
    Tensor.ContextLE 1
      (Tensor.relabel (readerParties e a z h)
        (Packing.Paired.short (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => A p.val) b))
      (Tensor.product (tensor (𝕜 := 𝕜) e a A) (tensor (𝕜 := 𝕜) e z B)) := by
  let R := readerParties e a z h
  let u : CyclicSchedule.Shared a z → ℕ := fun p => A p.val
  have hAB : (fun p : CyclicSchedule.Shared a z => B p.val) = u := by
    funext p
    exact (hshared p).symm
  have hl := tensor_context_selected (𝕜 := 𝕜) e a A (⟨z, h.symm⟩ : Input a)
    (by simpa only [hAz] using hb) (dualSharedInputEquiv a z h)
    (R.trans Packing.swapReaders) (readerParties_dual_selected e a z h)
  have hl' := selected_context_tensor (𝕜 := 𝕜) e a A (⟨z, h.symm⟩ : Input a)
    (by simpa only [hAz] using hb) (dualSharedInputEquiv a z h)
    (R.trans Packing.swapReaders) (readerParties_dual_selected e a z h)
  change Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e a A)
    (Tensor.relabel (R.trans Packing.swapReaders) (selected (𝕜 := 𝕜) u (A z))) at hl
  change Tensor.ContextLE 1
    (Tensor.relabel (R.trans Packing.swapReaders) (selected (𝕜 := 𝕜) u (A z)))
    (tensor (𝕜 := 𝕜) e a A) at hl'
  rw [hAz, ← Tensor.relabel_comp_indices] at hl hl'
  have hr := tensor_context_selected (𝕜 := 𝕜) e z B (⟨a, h⟩ : Input z)
    (by simpa only [hBa] using hb) (sharedInputEquiv a z h) R (readerParties_selected e a z h)
  have hr' := selected_context_tensor (𝕜 := 𝕜) e z B (⟨a, h⟩ : Input z)
    (by simpa only [hBa] using hb) (sharedInputEquiv a z h) R (readerParties_selected e a z h)
  change Tensor.ContextLE 1 (tensor (𝕜 := 𝕜) e z B)
    (Tensor.relabel R (selected (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => B p.val) (B a))) at hr
  change Tensor.ContextLE 1
    (Tensor.relabel R (selected (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => B p.val) (B a)))
    (tensor (𝕜 := 𝕜) e z B) at hr'
  rw [hBa, hAB] at hr hr'
  let C := selected (𝕜 := 𝕜) u b
  let D := Tensor.relabel Packing.swapReaders C
  have hc : Tensor.ContextLE 1 (Tensor.product D C) (Tensor.product C D) :=
    Tensor.ContextLE.of_reindex _ (Tensor.product_comm_reindex C D)
  have hc' : Tensor.ContextLE 1 (Tensor.product C D) (Tensor.product D C) :=
    Tensor.ContextLE.of_reindex _ (Tensor.product_comm_reindex D C)
  have hcR := hc.relabel R
  have hcR' := hc'.relabel R
  rw [Tensor.relabel_product, Tensor.relabel_product] at hcR hcR'
  constructor
  · have ht := (hl.product hr zero_le_one).trans hcR (by norm_num)
    simpa only [one_mul, R, C, D, u, Packing.Paired.short, Tensor.relabel_product] using ht
  · have ht := hcR'.trans (hl'.product hr' zero_le_one) zero_le_one
    simpa only [one_mul, R, C, D, u, Packing.Paired.short, Tensor.relabel_product] using ht

theorem pair_context_short (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z)
    (A B : ZMod k → ℕ) (b : ℕ) (hb : 0 < b)
    (hAz : A z = b) (hBa : B a = b)
    (hshared : ∀ p : CyclicSchedule.Shared a z, A p.val = B p.val) :
    Tensor.ContextLE 1
      (Tensor.product (tensor (𝕜 := 𝕜) e a A) (tensor (𝕜 := 𝕜) e z B))
      (Tensor.relabel (readerParties e a z h)
        (Packing.Paired.short (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => A p.val) b)) :=
  (pair_contexts e a z h A B b hb hAz hBa hshared).1

theorem short_context_pair (e : Fin k ≃ ZMod k) (a z : ZMod k) (h : a ≠ z)
    (A B : ZMod k → ℕ) (b : ℕ) (hb : 0 < b)
    (hAz : A z = b) (hBa : B a = b)
    (hshared : ∀ p : CyclicSchedule.Shared a z, A p.val = B p.val) :
    Tensor.ContextLE 1
      (Tensor.relabel (readerParties e a z h)
        (Packing.Paired.short (𝕜 := 𝕜) (fun p : CyclicSchedule.Shared a z => A p.val) b))
      (Tensor.product (tensor (𝕜 := 𝕜) e a A) (tensor (𝕜 := 𝕜) e z B)) :=
  (pair_contexts e a z h A B b hb hAz hBa hshared).2

/-- The fixed-output stage arrays match the local reader-dual pair exactly. -/
theorem stage_pair_shortening_of_local (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b)
    (l : ℕ) (hl : l < k - 1) (a : ZMod k) (c : ℕ)
    (hlocal : Tensor.ContextLE 1
      (Tensor.product
        (Packing.Paired.short (𝕜 := 𝕜)
          (fun p : CyclicSchedule.Shared a (CyclicSchedule.rightReader a l) =>
            CyclicSchedule.inputLength b l (a, false) p.val) b)
        (Packing.readerPairing (𝕜 := 𝕜) ((c + 2) ^ 2)))
      (Tensor.product
        (Packing.Paired.short (𝕜 := 𝕜)
          (fun p : CyclicSchedule.Shared a (CyclicSchedule.rightReader a l) =>
            CyclicSchedule.inputLength b l (a, false) p.val) (b + 1))
        (Packing.readerPairing (𝕜 := 𝕜) (c ^ 2)))) :
    Tensor.ContextLE 1
      (Tensor.product (shortenedPair (𝕜 := 𝕜) e b l a)
        (readerEdge (𝕜 := 𝕜) e a (CyclicSchedule.rightReader a l)
          (CyclicSchedule.readers_distinct a hl) ((c + 2) ^ 2)))
      (Tensor.product (stagePair (𝕜 := 𝕜) e b l a)
        (readerEdge (𝕜 := 𝕜) e a (CyclicSchedule.rightReader a l)
          (CyclicSchedule.readers_distinct a hl) (c ^ 2))) := by
  let z := CyclicSchedule.rightReader a l
  have h : a ≠ z := CyclicSchedule.readers_distinct a hl
  let A := CyclicSchedule.inputLength b l (a, false)
  let B := CyclicSchedule.inputLength b l (z, true)
  let A' := CyclicSchedule.inputLength b (l + 1) (a, false)
  let B' := CyclicSchedule.inputLength b (l + 1) (z, true)
  have hA : A z = b + 1 := (CyclicSchedule.paired_readers_long a b hl).2
  have hB : B a = b + 1 := by
    have hp := congrFun (CyclicSchedule.paired_inputLength a b l) a
    exact hp.trans (CyclicSchedule.paired_readers_long a b hl).1
  have hAB : ∀ p : CyclicSchedule.Shared a z, A p.val = B p.val := by
    intro p
    exact (congrFun (CyclicSchedule.paired_inputLength a b l) p.val).symm
  have hA' : A' z = b := by
    dsimp [A', z]
    rw [CyclicSchedule.inputLength_false_succ]
    simp
  have hB' : B' a = b := by
    dsimp [B', z]
    rw [CyclicSchedule.inputLength_paired_true_succ]
    simp
  have hsharedA : (fun p : CyclicSchedule.Shared a z => A' p.val) =
      (fun p : CyclicSchedule.Shared a z => A p.val) := by
    funext p
    change CyclicSchedule.inputLength b (l + 1) (a, false) p.val = A p.val
    rw [CyclicSchedule.inputLength_false_succ]
    exact Function.update_of_ne p.property.2 _ _
  have hAB' : ∀ p : CyclicSchedule.Shared a z, A' p.val = B' p.val := by
    intro p
    change CyclicSchedule.inputLength b (l + 1) (a, false) p.val =
      CyclicSchedule.inputLength b (l + 1) (CyclicSchedule.rightReader a l, true) p.val
    rw [CyclicSchedule.inputLength_false_succ, CyclicSchedule.inputLength_paired_true_succ,
      Function.update_of_ne p.property.2, Function.update_of_ne p.property.1]
  have ht := (pair_context_short (𝕜 := 𝕜) e a z h A' B' b hb hA' hB' hAB').rightTensor
    (readerEdge (𝕜 := 𝕜) e a z h ((c + 2) ^ 2))
  rw [hsharedA] at ht
  have hs := (short_context_pair (𝕜 := 𝕜) e a z h A B (b + 1) (by omega) hA hB hAB).rightTensor
    (readerEdge (𝕜 := 𝕜) e a z h (c ^ 2))
  have hp := hlocal.relabel (readerParties e a z h)
  rw [Tensor.relabel_product, Tensor.relabel_product] at hp
  have hall := (ht.trans hp zero_le_one).trans hs (by norm_num)
  simpa only [one_mul, stagePair, shortenedPair, stageFactor, A, B, A', B', z, readerEdge] using hall

/-- Every cyclic reader pair uses the same graph dimension `k * b`. -/
theorem stage_pair_shortening (e : Fin k ≃ ZMod k) (b : ℕ) (hb : 0 < b)
    (l : ℕ) (hl : l < k - 1) (a : ZMod k) :
    Tensor.ContextLE 1
      (Tensor.product (shortenedPair (𝕜 := 𝕜) e b l a)
        (readerEdge (𝕜 := 𝕜) e a (CyclicSchedule.rightReader a l)
          (CyclicSchedule.readers_distinct a hl) ((k * b + 2) ^ 2)))
      (Tensor.product (stagePair (𝕜 := 𝕜) e b l a)
        (readerEdge (𝕜 := 𝕜) e a (CyclicSchedule.rightReader a l)
          (CyclicSchedule.readers_distinct a hl) ((k * b) ^ 2))) := by
  apply stage_pair_shortening_of_local e b hb l hl a (k * b)
  apply Packing.Paired.shortening _ b (k * b)
  simpa only [Packing.count, degree] using CyclicSchedule.packing_condition a
    (CyclicSchedule.rightReader a l) (CyclicSchedule.readers_distinct a hl) b l (a, false)

end Lemmata.TensorRank.CyclicPolynomial
