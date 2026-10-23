module

public import Lemmata.SpanningTreeSymmetricEF.PolyhedralNormalForm
public import Lemmata.SpanningTreeSymmetricEF.OrbitCriterion

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF.LPResults

open ApproximationUpper CoordinateLowerBounds

/-- The Hamilton-path approximation threshold strictly exceeds one for n ≥ 4. -/
theorem one_lt_threshold (N : ℕ) (hN : 4 ≤ N) :
    (1 : ℝ) < (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)) := by
  apply (Approximation.threshold_exceeds_fixed_factor (N : ℝ) 1
    (by exact_mod_cast (show 0 < N by omega))).mpr
  norm_num
  exact_mod_cast (show 3 < N by omega)

variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

/-- An exact affine-symmetric LP extension of the genuine tree polytope has at
least choose(n,3) original inequalities for n ≥ 13, conditional only on the
explicit small-index group theorem. The symmetry is a genuine homomorphism;
feasible-set invariance and projection covariance are required only on feasible
points. The normal form, row action, and equivariant section are derived, not
assumed. No dimension, pointedness, strict-feasibility, or irredundancy condition
is imposed on the original description. -/
theorem exact_size_lower {N : ℕ}
    (Q : AffineSubspace ℝ E) (a : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ))
    (rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E))
    (hstable : ∀ g z, z ∈ feasible Q a → rho g z ∈ feasible Q a)
    (hp : ∀ g z, z ∈ feasible Q a → p (rho g z) = edgeAction N g (p z))
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N)
    (hexact : SignedLift.lpImage Q a p =
      convexHull ℝ (Set.range (treeIncidence (V := Fin N)))) :
    Nat.choose N 3 ≤ Fintype.card J := by
  exact PolyhedralNormalForm.affine_lp_size_lower Q a p rho hstable hp smallIndex hN
    1 (one_lt_threshold N (by omega))
    (OrbitCriterion.exact_tree_maxApproximation (by omega) hexact)

end Lemmata.SpanningTreeSymmetricEF.LPResults
