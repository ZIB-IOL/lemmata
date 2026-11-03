module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.PolynomialPacking
public import Lemmata.TensorRank.Proof.ContextTransport
public import Lemmata.TensorRank.Proof.PlacedReads
public import Lemmata.TensorRank.Proof.Degeneration

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct.Packing.Paired

variable {𝕜 : Type*} [Field 𝕜] {J : Type} [Fintype J]

def short (a : J → ℕ) (b : ℕ) :=
  Tensor.product (selected (𝕜 := 𝕜) a b)
    (Tensor.relabel swapReaders (selected (𝕜 := 𝕜) a b))

def input (a : J → ℕ) (b c : ℕ) :=
  Tensor.product (source (𝕜 := 𝕜) a b c)
    (Tensor.relabel swapReaders (source (𝕜 := 𝕜) a b c))

def diagonalSector (a : J → ℕ) (b c : ℕ) (l : Option (Fin (c + 1))) :=
  Tensor.product (sector (𝕜 := 𝕜) a b c l)
    (Tensor.relabel swapReaders (sector (𝕜 := 𝕜) a b c l))

def labelsEquiv (c : ℕ) : Fin (c + 2) ≃ Option (Fin (c + 1)) :=
  Fintype.equivOfCardEq (by simp)

def family (a : J → ℕ) (b c : ℕ) (l : Fin (c + 2)) :=
  sector (𝕜 := 𝕜) a b c (labelsEquiv c l)

theorem family_sum (a : J → ℕ) (b c : ℕ) :
    (∑ l, family (𝕜 := 𝕜) a b c l) = target (𝕜 := 𝕜) a b c := by
  unfold family
  rw [(labelsEquiv c).sum_comp, sum_sector]

theorem family_reads_input (a : J → ℕ) (b c : ℕ) :
    Tensor.Reads (family (𝕜 := 𝕜) a b c) (.inl false)
      (fun x => (labelsEquiv c).symm (inputLabel a b c x)) :=
  (sector_reads_input a b c).reindexLabels (labelsEquiv c)

theorem family_reads_output (a : J → ℕ) (b c : ℕ) :
    Tensor.Reads (family (𝕜 := 𝕜) a b c) (.inl true)
      (fun x => (labelsEquiv c).symm (outputLabel a b c x)) :=
  (sector_reads_output a b c).reindexLabels (labelsEquiv c)

def dualPairCoordinate (a : J → ℕ) (b : ℕ) (p : Bool ⊕ J) :
    (SelectedCoordinate a b (swapReaders p) ×
      SelectedCoordinate a b (swapReaders (swapReaders p))) ≃
        (SelectedCoordinate a b p × SelectedCoordinate a b (swapReaders p)) := by
  rcases p with ⟨⟨⟩⟩ | j <;> exact Equiv.prodComm _ _

theorem dualPair_reindex (a : J → ℕ) (b : ℕ) :
    Tensor.reindex (fun p => dualPairCoordinate a b p) (short (𝕜 := 𝕜) a b) =
      Tensor.product (Tensor.relabel swapReaders (selected (𝕜 := 𝕜) a b))
        (Tensor.relabel swapReaders
          (Tensor.relabel swapReaders (selected (𝕜 := 𝕜) a b))) := by
  funext x
  have h₁ : (fun p => (dualPairCoordinate a b p (x p)).2) =
      (fun p => (x p).1) := by
    funext p
    rcases p with ⟨⟨⟩⟩ | j <;> rfl
  have h₂ : (fun p => (dualPairCoordinate a b p (x p)).1) =
      Equiv.piCongrLeft (SelectedCoordinate a b) swapReaders
        (Equiv.piCongrLeft (fun p => SelectedCoordinate a b (swapReaders p))
          swapReaders (fun p => (x p).2)) := by
    funext p
    have hd (v : Bool ⊕ J) :
        Equiv.piCongrLeft (SelectedCoordinate a b) swapReaders
          (Equiv.piCongrLeft (fun p => SelectedCoordinate a b (swapReaders p))
            swapReaders (fun p => (x p).2)) (swapReaders (swapReaders v)) = (x v).2 := by
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
    rcases p with ⟨⟨⟩⟩ | j
    · exact (hd (.inl false)).symm
    · exact (hd (.inl true)).symm
    · exact (hd (.inr j)).symm
  change selected a b (fun p => (dualPairCoordinate a b p (x p)).1) *
      Tensor.relabel swapReaders (selected (𝕜 := 𝕜) a b)
        (fun p => (dualPairCoordinate a b p (x p)).2) = _
  rw [h₁, h₂]
  exact mul_comm _ _

theorem diagonalSector_context (a : J → ℕ) (b c : ℕ) (l : Option (Fin (c + 1))) :
    Tensor.ContextLE 1 (short (𝕜 := 𝕜) a b) (diagonalSector (𝕜 := 𝕜) a b c l) := by
  cases l with
  | some l =>
      simpa only [short, diagonalSector, one_mul] using
        (normal_restricts (𝕜 := 𝕜) a b c l).contextLE.product
          ((normal_restricts (𝕜 := 𝕜) a b c l).contextLE.relabel swapReaders) zero_le_one
  | none =>
      have h := (middle_restricts (𝕜 := 𝕜) a b c).contextLE
      have hp := h.product (h.relabel swapReaders) zero_le_one
      have hs := Tensor.ContextLE.of_reindex (fun p => dualPairCoordinate a b p)
        (dualPair_reindex (𝕜 := 𝕜) a b)
      simpa only [diagonalSector, one_mul] using hs.trans hp zero_le_one

theorem target_context (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c) :
    Tensor.ContextLE 1 (target (𝕜 := 𝕜) a b c) (source (𝕜 := 𝕜) a b c) := by
  intro U _ H
  have h := (target_degenerates (𝕜 := 𝕜) a b c hc).product (Tensor.Degenerates.refl H)
  simpa only [one_mul] using h.asymptoticRank_le

def wordPairCoordinate (a : J → ℕ) (b c N : ℕ) (p : Bool ⊕ J) :
    (Fin N → Coordinate a b c p × Coordinate a b c (swapReaders p)) ≃
      ((Fin N → Coordinate a b c p) × (Fin N → Coordinate a b c (swapReaders p))) :=
  Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Coordinate a b c p)
    (fun _ => Coordinate a b c (swapReaders p))

theorem wordPair_reindex (a : J → ℕ) (b c : ℕ) {N : ℕ} (w : Fin N → Fin (c + 2)) :
    Tensor.reindex (fun p => wordPairCoordinate a b c N p)
      (Tensor.product (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w)
        (Tensor.relabel swapReaders (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w))) =
      Tensor.wordTensor (fun l => diagonalSector (𝕜 := 𝕜) a b c (labelsEquiv c l)) w := by
  rw [Tensor.relabel_wordTensor]
  funext x
  change (∏ j, family (𝕜 := 𝕜) a b c (w j) (fun p => (x p j).1)) *
      (∏ j, Tensor.relabel swapReaders (family (𝕜 := 𝕜) a b c (w j))
        (fun p => (x p j).2)) = _
  exact (Finset.prod_mul_distrib : _).symm

theorem wordPair_context (a : J → ℕ) (b c : ℕ) {N : ℕ} (w : Fin N → Fin (c + 2)) :
    Tensor.ContextLE 1 (Tensor.power (short (𝕜 := 𝕜) a b) N)
      (Tensor.product (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w)
        (Tensor.relabel swapReaders (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w))) := by
  have hi := Tensor.ContextLE.indexedProduct_fin
    (S := fun _ : Fin N => short (𝕜 := 𝕜) a b)
    (T := fun j : Fin N => diagonalSector (𝕜 := 𝕜) a b c (labelsEquiv c (w j)))
    (c := fun _ => (1 : ℝ))
    (fun j => diagonalSector_context (𝕜 := 𝕜) a b c (labelsEquiv c (w j)))
    (fun _ => zero_le_one)
  have hi' : Tensor.ContextLE 1 (Tensor.power (short (𝕜 := 𝕜) a b) N)
      (Tensor.wordTensor (fun l => diagonalSector (𝕜 := 𝕜) a b c (labelsEquiv c l)) w) := by
    have hpow : Tensor.indexedProduct (fun _ : Fin N => short (𝕜 := 𝕜) a b) =
        Tensor.power (short (𝕜 := 𝕜) a b) N := by funext x; rfl
    have hword : Tensor.indexedProduct
        (fun j : Fin N => diagonalSector (𝕜 := 𝕜) a b c (labelsEquiv c (w j))) =
          Tensor.wordTensor (fun l => diagonalSector (𝕜 := 𝕜) a b c (labelsEquiv c l)) w := rfl
    rw [hpow, hword] at hi
    simpa only [Finset.prod_const_one] using hi
  have hr := (Tensor.reindex_restricts (fun p => wordPairCoordinate a b c N p)
    (Tensor.product (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w)
      (Tensor.relabel swapReaders (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w)))).contextLE
  rw [wordPair_reindex] at hr
  simpa only [one_mul] using hi'.trans hr zero_le_one

def swapPairCoordinate (d : ℕ) (p : Bool ⊕ J) :
    PairCoordinate d p ≃ PairCoordinate d (swapReaders p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> exact Equiv.refl _

set_option backward.isDefEq.respectTransparency false in
theorem swapPair_reindex (d : ℕ) :
    Tensor.reindex (fun p => swapPairCoordinate (J := J) d p)
      (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d)) =
      readerPairing (𝕜 := 𝕜) (J := J) d := by
  funext x
  let y : ∀ p, PairCoordinate d (swapReaders p) :=
    fun p => swapPairCoordinate (J := J) d p (x p)
  have hf : Equiv.piCongrLeft (PairCoordinate d) swapReaders y (.inl false) = x (.inl true) := by
    exact Equiv.piCongrLeft_apply_apply (PairCoordinate d) swapReaders y (.inl true)
  have ht : Equiv.piCongrLeft (PairCoordinate d) swapReaders y (.inl true) = x (.inl false) := by
    exact Equiv.piCongrLeft_apply_apply (PairCoordinate d) swapReaders y (.inl false)
  dsimp only [y] at hf ht
  dsimp only [Tensor.reindex, Tensor.relabel, readerPairing]
  rw [hf, ht]
  simp only [eq_comm]

theorem pairing_context_swap (d : ℕ) :
    Tensor.ContextLE 1 (readerPairing (𝕜 := 𝕜) (J := J) d)
      (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d)) := by
  have h := (Tensor.reindex_restricts (fun p => swapPairCoordinate (J := J) d p)
    (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d))).contextLE
  simpa only [swapPair_reindex] using h

theorem swapped_pairing_context (d : ℕ) :
    Tensor.ContextLE 1
      (Tensor.relabel swapReaders (readerPairing (𝕜 := 𝕜) (J := J) d))
      (readerPairing (𝕜 := 𝕜) (J := J) d) :=
  Tensor.ContextLE.of_reindex (fun p => swapPairCoordinate d p) (swapPair_reindex d)

def sharedPartyEquiv : Separation.Party (Fintype.card J) ≃ (Bool ⊕ J) :=
  Equiv.sumCongr (Equiv.refl Bool) (Fintype.equivFin J).symm

def sharedPairCoordinate (d : ℕ) (p : Bool ⊕ J) :
    PairCoordinate d p ≃ Separation.PairCoordinate d ((sharedPartyEquiv (J := J)).symm p) := by
  rcases p with ⟨⟨⟩⟩ | j <;> exact Equiv.refl _

set_option backward.isDefEq.respectTransparency false in
theorem sharedPair_reindex (d : ℕ) :
    Tensor.reindex (fun p => sharedPairCoordinate (J := J) d p)
      (Tensor.relabel (sharedPartyEquiv (J := J)).symm
        (Separation.readerPairing (𝕜 := 𝕜) (r := Fintype.card J) d)) =
      readerPairing (𝕜 := 𝕜) (J := J) d := by
  funext x
  let e := (sharedPartyEquiv (J := J)).symm
  let y : ∀ p, Separation.PairCoordinate d (e p) :=
    fun p => sharedPairCoordinate (J := J) d p (x p)
  have hf : Equiv.piCongrLeft (Separation.PairCoordinate d) e y (.inl false) = x (.inl false) := by
    exact Equiv.piCongrLeft_apply_apply (Separation.PairCoordinate d) e y (.inl false)
  have ht : Equiv.piCongrLeft (Separation.PairCoordinate d) e y (.inl true) = x (.inl true) := by
    exact Equiv.piCongrLeft_apply_apply (Separation.PairCoordinate d) e y (.inl true)
  dsimp only [e, y] at hf ht
  dsimp only [Tensor.reindex, Tensor.relabel, Separation.readerPairing, readerPairing]
  rw [hf, ht]

theorem fixed_type_context (a : J → ℕ) (b c : ℕ) {N : ℕ} (w : Fin N → Fin (c + 2)) :
    Tensor.ContextLE ((Fintype.card J + 2 : ℕ) : ℝ)
      (Tensor.product (readerPairing (𝕜 := 𝕜) (J := J) (Fintype.card (Types.Words (Types.histogram w))))
        (Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w))
      (Tensor.power (target (𝕜 := 𝕜) a b c) N) := by
  intro U _ H
  let e := sharedPartyEquiv (J := J)
  have hl := (family_reads_input (𝕜 := 𝕜) a b c).relabel e (.inl false)
  have hr := (family_reads_output (𝕜 := 𝕜) a b c).relabel e (.inl true)
  have h := Separation.fixed_type_bound_context
    (fun l => Tensor.relabel e (family (𝕜 := 𝕜) a b c l)) (Tensor.relabel e H) hl hr
    (⟨w, rfl⟩ : Types.Words (Types.histogram w))
  rw [← Tensor.relabel_sum, family_sum, ← Tensor.relabel_power,
    ← Tensor.relabel_product] at h
  rw [Tensor.asymptoticRank_relabel e
    (Tensor.product (Tensor.power (target (𝕜 := 𝕜) a b c) N) H)] at h
  rw [← Tensor.relabel_wordTensor, ← Tensor.relabel_product] at h
  rw [Tensor.asymptoticRank_product_assoc,
    ← sharedPair_reindex (𝕜 := 𝕜) (J := J) (Fintype.card (Types.Words (Types.histogram w))),
    Tensor.asymptoticRank_product_reindex,
    Tensor.asymptoticRank_relabel_context e]
  exact h

theorem paired_type_context_raw (a : J → ℕ) (b c : ℕ) (hc : count a b ≤ c)
    {N : ℕ} (w : Fin N → Fin (c + 2)) :
    Tensor.ContextLE (((Fintype.card J + 2 : ℕ) : ℝ) ^ 2)
      (Tensor.product
        (Tensor.product
          (readerPairing (𝕜 := 𝕜) (J := J) (Fintype.card (Types.Words (Types.histogram w))))
          (Tensor.relabel swapReaders
            (readerPairing (𝕜 := 𝕜) (J := J) (Fintype.card (Types.Words (Types.histogram w))))))
        (Tensor.power (short (𝕜 := 𝕜) a b) N))
      (Tensor.power (input (𝕜 := 𝕜) a b c) N) := by
  let E := readerPairing (𝕜 := 𝕜) (J := J) (Fintype.card (Types.Words (Types.histogram w)))
  let W := Tensor.wordTensor (family (𝕜 := 𝕜) a b c) w
  let Z := target (𝕜 := 𝕜) a b c
  have hw := (wordPair_context (𝕜 := 𝕜) a b c w).leftTensor
    (Tensor.product E (Tensor.relabel swapReaders E))
  have hs : Tensor.ContextLE 1
      (Tensor.product (Tensor.product E (Tensor.relabel swapReaders E))
        (Tensor.product W (Tensor.relabel swapReaders W)))
      (Tensor.product (Tensor.product E W)
        (Tensor.product (Tensor.relabel swapReaders E) (Tensor.relabel swapReaders W))) := by
    have he := Tensor.product_middle_reindex E (Tensor.relabel swapReaders E)
      W (Tensor.relabel swapReaders W)
    rw [← he]
    exact (Tensor.reindex_restricts _ _).contextLE
  have hb := (fixed_type_context (𝕜 := 𝕜) a b c w).product
    ((fixed_type_context (𝕜 := 𝕜) a b c w).relabel swapReaders) (Nat.cast_nonneg _)
  rw [Tensor.relabel_product, Tensor.relabel_power] at hb
  have hb' : Tensor.ContextLE (((Fintype.card J + 2 : ℕ) : ℝ) ^ 2)
      (Tensor.product (Tensor.product E W)
        (Tensor.product (Tensor.relabel swapReaders E) (Tensor.relabel swapReaders W)))
      (Tensor.product (Tensor.power Z N) (Tensor.power (Tensor.relabel swapReaders Z) N)) := by
    simpa only [pow_two] using hb
  have hp := Tensor.ContextLE.power_product Z (Tensor.relabel swapReaders Z) N
  have hd := ((target_context (𝕜 := 𝕜) a b c hc).product
    ((target_context (𝕜 := 𝕜) a b c hc).relabel swapReaders) zero_le_one).power N (by positivity)
  have hd' : Tensor.ContextLE 1
      (Tensor.power (Tensor.product Z (Tensor.relabel swapReaders Z)) N)
      (Tensor.power (input (𝕜 := 𝕜) a b c) N) := by
    simpa only [Z, input, one_mul, one_pow] using hd
  have h₁ := hw.trans hs zero_le_one
  have h₂ := h₁.trans hb' (by norm_num)
  have h₃ := h₂.trans hp (by positivity)
  simpa only [one_mul, mul_one] using h₃.trans hd' (by positivity)

end Lemmata.TensorRank.PolynomialProduct.Packing.Paired
