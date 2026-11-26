module

public import Lemmata.FrankWolfe.HilbertDefs
public import Lemmata.FrankWolfe.Proof.Rate
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-!
# From gradients to derivatives

In a Hilbert space the objects of `HilbertDefs.lean` are the objects of `Defs.lean` read through
the Riesz isometry `toDual : E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E`: an oracle on gradient vectors is an
oracle on functionals, `∇ f x = toDual.symm (fderiv ℝ f x)`, and the iterates coincide.
-/

namespace Lemmata.FrankWolfe

open scoped Gradient InnerProductSpace
open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The oracle on functionals induced by an oracle on gradient vectors. -/
noncomputable def dualLMO (lmo : E → E) : StrongDual ℝ E → E :=
  fun g => lmo ((toDual ℝ E).symm g)

theorem gradient_eq_symm (f : E → ℝ) (x : E) : ∇ f x = (toDual ℝ E).symm (fderiv ℝ f x) := rfl

theorem fderiv_eq_toDual (f : E → ℝ) (x : E) : fderiv ℝ f x = toDual ℝ E (∇ f x) := by
  rw [gradient_eq_symm, LinearIsometryEquiv.apply_symm_apply]

theorem hilbert_fwStep_eq (lmo : E → E) (f : E → ℝ) (x : E) (γ : ℝ) :
    Hilbert.fwStep lmo f x γ = fwStep (dualLMO lmo) (fderiv ℝ f) x γ := rfl

theorem hilbert_fwIterates_eq (lmo : E → E) (f : E → ℝ) (step : ℕ → E → ℝ) (x₀ : E) :
    Hilbert.fwIterates lmo f step x₀ = fwIterates (dualLMO lmo) (fderiv ℝ f) step x₀ := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change Hilbert.fwStep lmo f (Hilbert.fwIterates lmo f step x₀ t)
        (step t (Hilbert.fwIterates lmo f step x₀ t)) = _
    rw [ih]; rfl

theorem hilbert_shortStep_eq (lmo : E → E) (f : E → ℝ) (L : NNReal) :
    Hilbert.shortStep lmo f L = shortStep (dualLMO lmo) (fderiv ℝ f) L := by
  funext t x
  simp only [Hilbert.shortStep, shortStep, dualLMO, gradient_eq_symm, toDual_symm_apply]

theorem hilbert_isExactLineSearch_iff (lmo : E → E) (f : E → ℝ) (σ : E → ℝ) :
    Hilbert.IsExactLineSearch lmo f σ ↔ IsExactLineSearch (dualLMO lmo) f (fderiv ℝ f) σ :=
  Iff.rfl

theorem hilbert_standingAssumptions {C : Set E} {lmo : E → E} {f : E → ℝ} {L : NNReal}
    (h : Hilbert.StandingAssumptions C lmo f L) : StandingAssumptions C (dualLMO lmo) f L := by
  obtain ⟨hC, hconv, hlmo, hdiff, hcvx, hlip, hL⟩ := h
  refine ⟨hC, hconv, fun g => ⟨(hlmo _).1, fun y hy => ?_⟩, hcvx, ⟨hdiff, ?_⟩, hL⟩
  · have := (hlmo ((toDual ℝ E).symm g)).2 y hy
    simpa [dualLMO, toDual_symm_apply] using this
  · have hfd : fderiv ℝ f = (toDual ℝ E) ∘ (∇ f) := funext fun x => fderiv_eq_toDual f x
    rw [hfd]
    simpa using (toDual ℝ E).lipschitzWith.comp hlip

end Lemmata.FrankWolfe
