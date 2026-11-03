module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialPacking
public import Lemmata.TensorRank.Proof.PairingGraph

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PlacedPairing

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} {J : Type} [Fintype J]

omit [Fintype J] in
theorem readers_ne (d : Fin k ≃ (Bool ⊕ J)) : d.symm (.inl false) ≠ d.symm (.inl true) := by
  intro h
  have hh := d.symm.injective h
  cases hh

def edge (d : Fin k ≃ (Bool ⊕ J)) : Edge k :=
  edgeBetween (d.symm (.inl false)) (d.symm (.inl true)) (readers_ne d).symm

def coordinate (d : Fin k ≃ (Bool ⊕ J)) (c : ℕ) (p : Bool ⊕ J) :
    PolynomialProduct.Packing.PairCoordinate c p ≃
      WeightedCoordinate (singleEdgeDimensions (edge d) c) (d.symm p) :=
  match p with
  | .inl false => singleEdgeCoordinate _ c _ (by simp [edge, edgeBetween])
  | .inl true => singleEdgeCoordinate _ c _ (by simp [edge, edgeBetween])
  | .inr j => singleEdgeInactiveCoordinate _ c _ (by
      intro h
      simp only [edge, edgeBetween, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with ha | hb
      · have hh := d.symm.injective ha
        cases hh
      · have hh := d.symm.injective hb
        cases hh)

theorem pairing_reindex (d : Fin k ≃ (Bool ⊕ J)) (c : ℕ) :
    Tensor.reindex (fun p => coordinate d c p)
      (Tensor.relabel d.symm (weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c))) =
        PolynomialProduct.Packing.readerPairing c := by
  funext x
  let y := Equiv.piCongrLeft (WeightedCoordinate (singleEdgeDimensions (edge d) c)) d.symm
    (fun p => coordinate d c p (x p))
  have hy (p : Bool ⊕ J) : y (d.symm p) = coordinate d c p (x p) := by simp [y]
  have ha : (y (d.symm (.inl false)) ⟨edge d, by simp [edge, edgeBetween]⟩).val =
      (x (.inl false)).val := by
    rw [hy]
    exact singleEdgeCoordinate_value (edge d) c _ _ (x (.inl false))
  have hb : (y (d.symm (.inl true)) ⟨edge d, by simp [edge, edgeBetween]⟩).val =
      (x (.inl true)).val := by
    rw [hy]
    exact singleEdgeCoordinate_value (edge d) c _ _ (x (.inl true))
  change weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c) y =
    PolynomialProduct.Packing.readerPairing c x
  change (if ∀ (f : Edge k) (i j : Fin k) (hi : i ∈ f.val) (hj : j ∈ f.val),
      y i ⟨f, hi⟩ = y j ⟨f, hj⟩ then 1 else 0) = _
  have hsupport :
      (∀ (f : Edge k) (i j : Fin k) (hi : i ∈ f.val) (hj : j ∈ f.val),
        y i ⟨f, hi⟩ = y j ⟨f, hj⟩) ↔
      (y (d.symm (.inl false)) ⟨edge d, by simp [edge, edgeBetween]⟩).val =
        (y (d.symm (.inl true)) ⟨edge d, by simp [edge, edgeBetween]⟩).val := by
    simpa only [edge] using
      (weighted_single_support_iff (d.symm (.inl false)) (d.symm (.inl true)) (readers_ne d) c y)
  simp only [hsupport]
  rw [ha, hb]
  simp only [PolynomialProduct.Packing.readerPairing, Fin.ext_iff]

theorem context_rank (d : Fin k ≃ (Bool ⊕ J)) (c : ℕ)
    {U : Fin k → Type} [∀ i, Fintype (U i)] (H : Tensor 𝕜 (Fin k) U) :
    Tensor.asymptoticRank (Tensor.product
      (Tensor.relabel d (PolynomialProduct.Packing.readerPairing c)) H) =
      Tensor.asymptoticRank (Tensor.product
        (weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c)) H) := by
  let G := weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c)
  have hcontext := Tensor.asymptoticRank_relabel_context d.symm
    (PolynomialProduct.Packing.readerPairing (𝕜 := 𝕜) c) H
  simp only [Equiv.symm_symm] at hcontext
  rw [hcontext, ← pairing_reindex d c,
    Tensor.asymptoticRank_product_reindex (Tensor.relabel d.symm G) (Tensor.relabel d.symm H)
      (fun p => coordinate d c p),
    ← Tensor.relabel_product d.symm G H]
  exact Tensor.asymptoticRank_relabel d.symm (Tensor.product G H)

theorem pairing_contextLE_weighted (d : Fin k ≃ (Bool ⊕ J)) (c : ℕ) :
    Tensor.ContextLE 1 (Tensor.relabel d (PolynomialProduct.Packing.readerPairing c))
      (weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c)) := by
  intro U _ H
  rw [one_mul]
  exact (context_rank d c H).le

theorem weighted_contextLE_pairing (d : Fin k ≃ (Bool ⊕ J)) (c : ℕ) :
    Tensor.ContextLE 1 (weightedComplete (𝕜 := 𝕜) (singleEdgeDimensions (edge d) c))
      (Tensor.relabel d (PolynomialProduct.Packing.readerPairing c)) := by
  intro U _ H
  rw [one_mul]
  exact (context_rank d c H).ge

end Lemmata.TensorRank.PlacedPairing
