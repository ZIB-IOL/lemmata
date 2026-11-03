module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Proof.PolynomialTransport
public import Lemmata.TensorRank.Proof.ContextTransport

@[expose] public section

set_option autoImplicit false

open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {𝕜 : Type*} [Field 𝕜]
variable {k : ℕ} {J : Type} [Fintype J]

noncomputable def placed (e : Fin k ≃ Option J) (a : J → ℕ) :=
  Tensor.relabel e (tensor (𝕜 := 𝕜) a)

def selectedParties (e : Fin k ≃ Option J) (j : J) : Fin k ≃ (Bool ⊕ Other j) :=
  e.trans (inputPartyEquiv j).symm

theorem selectedParties_comp (e : Fin k ≃ Option J) (j : J) :
    (selectedParties e j).trans (inputPartyEquiv j) = e := by
  apply Equiv.ext
  intro i
  change inputPartyEquiv j ((inputPartyEquiv j).symm (e i)) = e i
  exact (inputPartyEquiv j).apply_symm_apply (e i)

private theorem context_relabel_left {I K : Type} [Fintype I] [Fintype K]
    {V : I → Type} [∀ i, Fintype (V i)] {W : K → Type} [∀ i, Fintype (W i)]
    (e f : K ≃ I) (hef : e = f) (S : Tensor 𝕜 I V) (T : Tensor 𝕜 K W) :
    Tensor.ContextLE 1 (Tensor.relabel e S) T ↔ Tensor.ContextLE 1 (Tensor.relabel f S) T := by
  subst f
  rfl

private theorem context_relabel_right {I K : Type} [Fintype I] [Fintype K]
    {V : I → Type} [∀ i, Fintype (V i)] {W : K → Type} [∀ i, Fintype (W i)]
    (e f : K ≃ I) (hef : e = f) (S : Tensor 𝕜 K W) (T : Tensor 𝕜 I V) :
    Tensor.ContextLE 1 S (Tensor.relabel e T) ↔ Tensor.ContextLE 1 S (Tensor.relabel f T) := by
  subst f
  rfl

theorem placed_context_selected (e : Fin k ≃ Option J)
    (a : J → ℕ) (j : J) (hj : 0 < a j) :
    Tensor.ContextLE 1 (placed (𝕜 := 𝕜) e a)
      (Tensor.relabel (selectedParties e j) (selected (𝕜 := 𝕜) (remaining a j) (a j))) := by
  have h := Tensor.ContextLE.of_reindex (inputCoordinateEquiv a j hj)
    (selected_relabel_tensor (𝕜 := 𝕜) a j hj)
  have ht := h.relabel (selectedParties e j)
  rw [Tensor.relabel_comp_indices] at ht
  exact (context_relabel_left _ _ (selectedParties_comp e j) _ _).mp ht

theorem selected_context_placed (e : Fin k ≃ Option J)
    (a : J → ℕ) (j : J) (hj : 0 < a j) :
    Tensor.ContextLE 1
      (Tensor.relabel (selectedParties e j) (selected (𝕜 := 𝕜) (remaining a j) (a j)))
      (placed (𝕜 := 𝕜) e a) := by
  have he : Tensor.reindex (fun p => (inputCoordinateEquiv a j hj p).symm)
      (selected (𝕜 := 𝕜) (remaining a j) (a j)) =
        Tensor.relabel (inputPartyEquiv j) (tensor (𝕜 := 𝕜) a) := by
    rw [← selected_relabel_tensor (𝕜 := 𝕜) a j hj]
    funext x
    simp only [Tensor.reindex, Equiv.apply_symm_apply]
  have h := Tensor.ContextLE.of_reindex (fun p => (inputCoordinateEquiv a j hj p).symm) he
  have ht := h.relabel (selectedParties e j)
  rw [Tensor.relabel_comp_indices] at ht
  exact (context_relabel_right _ _ (selectedParties_comp e j) _ _).mp ht

theorem remaining_update (a : J → ℕ) (j : J) (b : ℕ) :
    remaining (Function.update a j b) j = remaining a j := by
  funext i
  exact Function.update_of_ne i.property _ _

end Lemmata.TensorRank.PolynomialProduct
