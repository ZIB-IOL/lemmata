module

public import Lemmata.Centroid.Proof.Symmetric.Graph
public import Lemmata.Centroid.Proof.Symmetric.Filtration
public import Lemmata.Centroid.Proof.Symmetric.Centroid
public import Lemmata.Centroid.Proof.Symmetric.LowerBound
public import Lemmata.Centroid.Proof.Tensor.FieldExtension
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

namespace Lemmata.Centroid

open Lemmata.Centroid.Symmetric

variable {F I : Type*} [Field F] [Infinite F] [Fintype I]

theorem symmetric_reduction_bound
    (E S : Submodule F (Coefficients F I 3)) (v : I → F) (m N : ℕ)
    (hSE : S ≤ E) (hSv : S ≤ (contraction 2 v).ker)
    (hmax : ∀ w : I → F,
      Module.finrank F (E.map (contraction 2 w)) ≤ Module.finrank F (E.map (contraction 2 v)))
    (hcontraction : Module.finrank F (E.map (contraction 2 v)) + 1 ≤ m)
    (hsupport : m + Module.finrank F (oneSupport S) ≤ N) :
    m + Module.finrank F S ≤ symmetricBound N := by
  classical
  have hf := contraction_filtration_bound E S v hSE hSv hmax
  have hg := graph_bound S
  apply symmetric_completion (m := m) (y := Module.finrank F S)
    (ρ := Module.finrank F (oneSupport S))
    (b := Module.finrank F (quadraticShadow S) + Module.finrank F (doubleShadow S) +
      Module.finrank F (tripleShadow S)) (N := N) hsupport
  · omega
  · simpa only [Nat.add_assoc] using hg

theorem symmetric_coefficients_upper_bound_infinite [Nonempty I]
    (c : Coefficients F I 3) (hc : Tensor.Concise (toTensor 3 c)) :
    Module.finrank F (Tensor.centroid (toTensor 3 c)) ≤ symmetricBound (Fintype.card I) := by
  obtain ⟨m, E, S, v, hdim, hsupport, hSE, hSv, hmax, hcontraction⟩ :=
    CentroidModel.exists_reduction c hc
  rw [hdim]
  exact symmetric_reduction_bound E S v m (Fintype.card I) hSE hSv hmax hcontraction hsupport

theorem symmetric_centroid_upper_bound_infinite [Nonempty I]
    {T : Cubic F I} (hc : Tensor.Concise T) (hs : Cubic.IsSymmetric T) :
    Module.finrank F (Tensor.centroid T) ≤ symmetricBound (Fintype.card I) := by
  let c := coordinatesEquiv.symm ⟨T, hs⟩
  have hT : toTensor 3 c = T :=
    congrArg Subtype.val (coordinatesEquiv.apply_symm_apply ⟨T, hs⟩)
  have hc' : Tensor.Concise (toTensor 3 c) := hT ▸ hc
  rw [← hT]
  exact symmetric_coefficients_upper_bound_infinite c hc'

omit [Infinite F] in
theorem symmetric_centroid_upper_bound {T : Cubic F I}
    (hc : Tensor.Concise T) (hs : Cubic.IsSymmetric T) :
    Module.finrank F (Tensor.centroid T) ≤ symmetricBound (Fintype.card I) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let _ : IsEmpty I := hI
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr hI =>
    let _ : Nonempty I := hI
    let K := RatFunc F
    let φ : F →+* K := algebraMap F K
    let _ : Infinite K := Infinite.of_injective
      (algebraMap (Polynomial F) K) (RatFunc.algebraMap_injective F)
    have hc' : Tensor.Concise (φ ∘ T) := hc.map φ
    have hs' : Cubic.IsSymmetric (φ ∘ T) := by
      intro σ x
      exact congrArg φ (hs σ x)
    have h := symmetric_centroid_upper_bound_infinite hc' hs'
    rwa [Tensor.finrank_centroid_map] at h

omit [Infinite F] in
theorem exists_symmetric_maximizer (N : ℕ) :
    ∃ T : Cubic F (Fin N), Tensor.Concise T ∧ Cubic.IsSymmetric T ∧
      Module.finrank F (Tensor.centroid T) = symmetricBound N := by
  obtain ⟨T, hc, hs, hlower⟩ := Construction.symmetric_lower_bound (F := F) N
  refine ⟨T, hc, hs, le_antisymm ?_ hlower⟩
  simpa only [Fintype.card_fin] using symmetric_centroid_upper_bound hc hs

def symmetricCentroidDimensions (F : Type*) [Field F] (N : ℕ) : Set ℕ :=
  {d | ∃ T : Cubic F (Fin N), Tensor.Concise T ∧ Cubic.IsSymmetric T ∧
    Module.finrank F (Tensor.centroid T) = d}

omit [Infinite F] in
theorem symmetric_maximum (N : ℕ) :
    IsGreatest (symmetricCentroidDimensions F N) (symmetricBound N) := by
  constructor
  · exact exists_symmetric_maximizer N
  · rintro d ⟨T, hc, hs, rfl⟩
    simpa only [Fintype.card_fin] using symmetric_centroid_upper_bound hc hs

omit [Infinite F] in
theorem symmetric_maximum_at {N n s : ℕ} (hN₂ : 2 ≤ N) (hs : s ≤ n + 1)
    (hN : N = symmetricBase n + s) :
    IsGreatest (symmetricCentroidDimensions F N)
      ((n + 2).choose 3 + 1 + max s (s.choose 2)) := by
  have h := symmetric_maximum (F := F) N
  rw [symmetricBound_eq hN₂ hs hN] at h
  exact h

end Lemmata.Centroid
