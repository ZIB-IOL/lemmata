module

/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

public import Lemmata.TensorRank.Def.PolynomialProduct
public import Lemmata.TensorRank.Proof.ContextTransport

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.PolynomialProduct

variable {𝕜 : Type*} [Field 𝕜]
variable {J K : Type} [Fintype J] [Fintype K]

theorem degree_comp_equiv (s : J ≃ K) (a : K → ℕ) :
    degree (a ∘ s) = degree a := by
  exact s.sum_comp (fun j => a j - 1)

def selectedInputCoordinateEquiv (s : J ≃ K) (a : K → ℕ) (b : ℕ)
    (p : Bool ⊕ J) :
    SelectedCoordinate (a ∘ s) b p ≃
      SelectedCoordinate a b ((Equiv.sumCongr (Equiv.refl Bool) s) p) :=
  match p with
  | .inl false => Equiv.refl _
  | .inl true => finCongr (congrArg (fun d => b + d) (degree_comp_equiv s a))
  | .inr _ => Equiv.refl _

/-- Reindexing the shared inputs of a polynomial tensor only permutes its summation variables. -/
theorem selected_relabel_inputs (s : J ≃ K) (a : K → ℕ) (b : ℕ) :
    Tensor.reindex (fun p => selectedInputCoordinateEquiv s a b p)
      (Tensor.relabel (Equiv.sumCongr (Equiv.refl Bool) s) (selected (𝕜 := 𝕜) a b)) =
        selected (𝕜 := 𝕜) (a ∘ s) b := by
  funext x
  let e := Equiv.sumCongr (Equiv.refl Bool) s
  let y : ∀ p, SelectedCoordinate a b p :=
    Equiv.piCongrLeft (SelectedCoordinate a b) e
      (fun p => selectedInputCoordinateEquiv s a b p (x p))
  have hy₀ : (y (.inl false)).val = (x (.inl false)).val := by
    change ((Equiv.piCongrLeft (SelectedCoordinate a b) e
      (fun p => selectedInputCoordinateEquiv s a b p (x p))) (e (.inl false))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hy₁ : (y (.inl true)).val = (x (.inl true)).val := by
    change ((Equiv.piCongrLeft (SelectedCoordinate a b) e
      (fun p => selectedInputCoordinateEquiv s a b p (x p))) (e (.inl true))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hyj (j : J) : (y (.inr (s j))).val = (x (.inr j)).val := by
    change ((Equiv.piCongrLeft (SelectedCoordinate a b) e
      (fun p => selectedInputCoordinateEquiv s a b p (x p))) (e (.inr j))).val = _
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hs : (∑ j : K, (y (.inr j)).val) = ∑ j : J, (x (.inr j)).val := by
    rw [← s.sum_comp (fun j => (y (.inr j)).val)]
    exact Finset.sum_congr rfl (fun j _ => hyj j)
  change (if (y (.inl false)).val + (∑ j, (y (.inr j)).val) = (y (.inl true)).val
    then (1 : 𝕜) else 0) = _
  rw [hy₀, hy₁, hs]
  rfl

theorem relabel_inputs_context_selected (s : J ≃ K) (a : K → ℕ) (b : ℕ) :
    Tensor.ContextLE 1
      (Tensor.relabel (Equiv.sumCongr (Equiv.refl Bool) s) (selected (𝕜 := 𝕜) a b))
      (selected (𝕜 := 𝕜) (a ∘ s) b) :=
  Tensor.ContextLE.of_reindex (selectedInputCoordinateEquiv s a b)
    (selected_relabel_inputs s a b)

theorem selected_context_relabel_inputs (s : J ≃ K) (a : K → ℕ) (b : ℕ) :
    Tensor.ContextLE 1 (selected (𝕜 := 𝕜) (a ∘ s) b)
      (Tensor.relabel (Equiv.sumCongr (Equiv.refl Bool) s) (selected (𝕜 := 𝕜) a b)) := by
  apply Tensor.ContextLE.of_reindex (fun p => (selectedInputCoordinateEquiv s a b p).symm)
  rw [← selected_relabel_inputs s a b]
  funext x
  simp only [Tensor.reindex, Equiv.apply_symm_apply]

end Lemmata.TensorRank.PolynomialProduct
