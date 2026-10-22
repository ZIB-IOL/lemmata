module

public import Lemmata.SpanningTreeSymmetricEF.PrimalPSDBound
public import Lemmata.SpanningTreeSymmetricEF.SignedLift
public import Lemmata.SpanningTreeSymmetricEF.ApproximationUpper

@[expose] public section


/-! Full-coordinate geometric formulation-size bound. The baseline tree and
restriction to its nonedges are constructed, not additional model hypotheses.
No factorization, conic-duality, strict-feasibility or symmetry input is needed. -/
namespace Lemmata.SpanningTreeSymmetricEF.NonnegativeOuter
open scoped BigOperators
open ApproximationUpper
noncomputable section
variable {V E B : Type*} [Fintype V] [Nonempty V]
variable [AddCommGroup E] [Module ℝ E] [Fintype B]
variable {K : B → Type*} [∀ b, Fintype (K b)]

/-- Every actual affine product-PSD lift containing actual trees and projecting
into the nonnegative orthant has size at least choose(|V|-1,2). -/
theorem sdp_size_lower (S : AffineSubspace ℝ E)
    (M : ∀ b, E →ᵃ[ℝ] Matrix (K b) (K b) ℝ)
    (p : E →ᵃ[ℝ] (Sym2 V → ℝ))
    (hcontains : ∀ T : SpanningTree V, treeIncidence T ∈ SignedLift.psdImage S M p)
    (hnonneg : ∀ x ∈ SignedLift.psdImage S M p, ∀ e, 0 ≤ x e) :
    (Fintype.card V - 1).choose 2 ≤ ∑ b, Fintype.card (K b) := by
  classical
  obtain ⟨T₀, _, hT₀⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le
  let restrict : (Sym2 V → ℝ) →ₗ[ℝ] (IdentitySlack.Nonedge T₀ → ℝ) :=
    { toFun := fun x e => x e.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply PrimalPSDBound.tree_sum_order_bound_of_affine_psd_lift T₀ hT₀ S M
    (restrict.toAffineMap.comp p)
  · intro T hT
    obtain ⟨z, hz, hM, hp⟩ := hcontains ⟨T,hT⟩
    refine ⟨z, hz, hM, ?_⟩
    intro e
    change p z e.val = _
    rw [hp]
    rfl
  · intro z hz hM e
    exact hnonneg (p z) ⟨z,hz,hM,rfl⟩ e.val

/-- Paper-facing version with containment of the whole tree polytope. The
stronger vertex-only endpoint above is used internally. -/
theorem sdp_size_lower_of_polytope_containment (S : AffineSubspace ℝ E)
    (M : ∀ b, E →ᵃ[ℝ] Matrix (K b) (K b) ℝ)
    (p : E →ᵃ[ℝ] (Sym2 V → ℝ))
    (hcontains : convexHull ℝ (Set.range (treeIncidence (V := V))) ⊆
      SignedLift.psdImage S M p)
    (hnonneg : ∀ x ∈ SignedLift.psdImage S M p, ∀ e, 0 ≤ x e) :
    (Fintype.card V - 1).choose 2 ≤ ∑ b, Fintype.card (K b) :=
  sdp_size_lower S M p (fun T => hcontains (subset_convexHull ℝ _ ⟨T,rfl⟩)) hnonneg

end
end Lemmata.SpanningTreeSymmetricEF.NonnegativeOuter
