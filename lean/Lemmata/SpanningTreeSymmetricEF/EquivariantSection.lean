module

public import Lemmata.SpanningTreeSymmetricEF.SignedLift
public import Mathlib.Analysis.Convex.Combination

@[expose] public section


/-! Averaging actual preimages gives an equivariant section of a convex lift.
No section, orbit positivity, or signed-point feasibility is assumed. -/
namespace Lemmata.SpanningTreeSymmetricEF.EquivariantSection
open scoped BigOperators
noncomputable section

variable {G T E F : Type*} [Group G] [Fintype G] [MulAction G T]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Explicit Reynolds average of arbitrary preimages. -/
def average (rho : G →* (E ≃ᵃ[ℝ] E)) (u : T → E) (t : T) : E :=
  ∑ g : G, (Fintype.card G : ℝ)⁻¹ • rho g (u (g⁻¹ • t))

theorem weights_sum : (∑ _g : G, (Fintype.card G : ℝ)⁻¹) = 1 := by
  have h : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [h]

theorem average_mem (rho : G →* (E ≃ᵃ[ℝ] E)) (Q : Set E)
    (hQ : Convex ℝ Q) (hstable : ∀ g z, z ∈ Q → rho g z ∈ Q)
    (u : T → E) (hu : ∀ t, u t ∈ Q) (t : T) : average rho u t ∈ Q := by
  apply hQ.sum_mem
  · intro g _
    positivity
  · simp
  · intro g _
    exact hstable g _ (hu _)

theorem average_projection (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ᵃ[ℝ] F)) (p : E →ᵃ[ℝ] F) (v : T → F)
    (hp : ∀ g z, p (rho g z) = eta g (p z))
    (hv : ∀ g t, v (g • t) = eta g (v t))
    (u : T → E) (hu : ∀ t, p (u t) = v t) (t : T) :
    p (average rho u t) = v t := by
  rw [average, SignedLift.map_weighted_sum p _ _ (weights_sum (G := G))]
  have hh (g : G) : p (rho g (u (g⁻¹ • t))) = v t := by
    rw [hp, hu, ← hv, smul_inv_smul]
  simp_rw [hh]
  rw [← Finset.sum_smul, weights_sum, one_smul]

theorem average_equivariant (rho : G →* (E ≃ᵃ[ℝ] E)) (u : T → E)
    (h : G) (t : T) : average rho u (h • t) = rho h (average rho u t) := by
  change (∑ g : G, (Fintype.card G : ℝ)⁻¹ • rho g (u (g⁻¹ • h • t))) =
    (rho h).toAffineMap (∑ g : G, (Fintype.card G : ℝ)⁻¹ • rho g (u (g⁻¹ • t)))
  rw [SignedLift.map_weighted_sum _ _ _ (weights_sum (G := G))]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft h)
  intro g
  simp [map_mul, mul_smul]

/-- Actual feasible preimages suffice; the resulting section is feasible,
projects exactly, and is equivariant for the given affine actions. -/
theorem exists_equivariant_section (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ᵃ[ℝ] F)) (Q : Set E) (hQ : Convex ℝ Q)
    (hstable : ∀ g z, z ∈ Q → rho g z ∈ Q)
    (p : E →ᵃ[ℝ] F) (v : T → F)
    (hp : ∀ g z, p (rho g z) = eta g (p z))
    (hv : ∀ g t, v (g • t) = eta g (v t))
    (hpre : ∀ t, ∃ z ∈ Q, p z = v t) :
    ∃ s : T → E, (∀ t, s t ∈ Q) ∧ (∀ t, p (s t) = v t) ∧
      ∀ g t, s (g • t) = rho g (s t) := by
  choose u hu hp' using hpre
  exact ⟨average rho u, average_mem rho Q hQ hstable u hu,
    average_projection rho eta p v hp hv u hp', average_equivariant rho u⟩

end
end Lemmata.SpanningTreeSymmetricEF.EquivariantSection
