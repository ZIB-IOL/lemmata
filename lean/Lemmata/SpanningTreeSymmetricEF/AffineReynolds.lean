module

public import Lemmata.SpanningTreeSymmetricEF.CoordinateLowerBounds

@[expose] public section


/-! Finite-group Reynolds averaging for affine polyhedra and projections.
Strictness only uses the identity summand, not a permutation of the slacks.
The projection average agrees with the original map on any set on which that
map was already equivariant. -/
namespace Lemmata.SpanningTreeSymmetricEF.AffineReynolds

open scoped BigOperators
noncomputable section

variable {G E F I : Type*} [Group G] [Fintype G]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- A finite affine symmetry group preserving a polyhedron has a fixed strictly
feasible point whenever a strictly feasible point exists. The constraint index
type need not be finite or inhabited. -/
theorem exists_fixed_strict
    (Q : AffineSubspace ℝ E) (a : I → E →ᵃ[ℝ] ℝ)
    (rho : G →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ CoordinateLowerBounds.feasible Q a →
      rho g z ∈ CoordinateLowerBounds.feasible Q a)
    (o : E) (ho : o ∈ Q) (ha : ∀ i, 0 < a i o) :
    ∃ ostar ∈ CoordinateLowerBounds.feasible Q a,
      (∀ i, 0 < a i ostar) ∧ ∀ g, rho g ostar = ostar := by
  classical
  have hop : o ∈ CoordinateLowerBounds.feasible Q a := ⟨ho, fun i => (ha i).le⟩
  let u : G → E := fun _ => o
  let ostar := EquivariantSection.average rho u (1 : G)
  refine ⟨ostar, EquivariantSection.average_mem rho _
    (CoordinateLowerBounds.feasible_convex Q a) hstable u (fun _ => hop) 1, ?_, ?_⟩
  · intro i
    change 0 < a i (∑ g : G, (Fintype.card G : ℝ)⁻¹ • rho g o)
    rw [SignedLift.map_weighted_sum (a i) _ _ (EquivariantSection.weights_sum (G := G))]
    apply Finset.sum_pos'
    · intro g _
      exact smul_nonneg (by positivity) ((hstable g o hop).2 i)
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      simpa using mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos) :
        0 < (Fintype.card G : ℝ)⁻¹) (ha i)
  · intro g
    have h := EquivariantSection.average_equivariant rho u g (1 : G)
    simpa [ostar, EquivariantSection.average, u] using h.symm

/-- Average the conjugates of an affine projection. The target action is linear,
so this is an affine map without any restriction on the source action's origin. -/
def avgProjection (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ₗ[ℝ] F)) (p : E →ᵃ[ℝ] F) : E →ᵃ[ℝ] F :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G,
    (eta g⁻¹).toLinearMap.toAffineMap.comp (p.comp (rho g).toAffineMap)

/-- Pointwise formula for the affine Reynolds operator. -/
theorem avgProjection_apply (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ₗ[ℝ] F)) (p : E →ᵃ[ℝ] F) (z : E) :
    avgProjection rho eta p z =
      ∑ g : G, (Fintype.card G : ℝ)⁻¹ • eta g⁻¹ (p (rho g z)) := by
  classical
  have heval (s : Finset G) (f : G → E →ᵃ[ℝ] F) :
      (∑ g ∈ s, f g) z = ∑ g ∈ s, f g z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert g s hg ih => simp [hg, ih]
  simp only [avgProjection, AffineMap.coe_smul, Pi.smul_apply, heval,
    AffineMap.comp_apply, LinearMap.coe_toAffineMap, LinearEquiv.coe_coe,
    AffineEquiv.coe_toAffineMap, Finset.smul_sum]

/-- Averaging produces equivariance on the whole ambient space. -/
theorem avgProjection_equivariant (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ₗ[ℝ] F)) (p : E →ᵃ[ℝ] F) (h : G) (z : E) :
    avgProjection rho eta p (rho h z) = eta h (avgProjection rho eta p z) := by
  simp only [avgProjection_apply, map_sum, map_smul]
  symm
  apply Fintype.sum_equiv (Equiv.mulRight h⁻¹)
  intro g
  simp [map_mul, AffineEquiv.inv_def]

/-- On any set where the original projection is equivariant, averaging leaves
it unchanged. No stability or convexity assumption on this set is needed. -/
theorem avgProjection_eq_on (rho : G →* (E ≃ᵃ[ℝ] E))
    (eta : G →* (F ≃ₗ[ℝ] F)) (p : E →ᵃ[ℝ] F) (P : Set E)
    (hp : ∀ g z, z ∈ P → p (rho g z) = eta g (p z))
    (z : E) (hz : z ∈ P) : avgProjection rho eta p z = p z := by
  rw [avgProjection_apply]
  have hh (g : G) : eta g⁻¹ (p (rho g z)) = p z := by
    rw [hp g z hz]
    change (eta g⁻¹ * eta g) (p z) = p z
    rw [← map_mul]
    simp
  simp_rw [hh]
  rw [← Finset.sum_smul, EquivariantSection.weights_sum, one_smul]

end
end Lemmata.SpanningTreeSymmetricEF.AffineReynolds
