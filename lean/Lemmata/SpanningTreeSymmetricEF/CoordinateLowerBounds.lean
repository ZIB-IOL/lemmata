module

public import Lemmata.SpanningTreeSymmetricEF.EquivariantSection
public import Lemmata.SpanningTreeSymmetricEF.Assumptions
public import Lemmata.SpanningTreeSymmetricEF.HamiltonPath

@[expose] public section


/-! Lower bounds for actual affine lifts with normalized coordinate-permuted
scalar slacks. These are not themselves normal-form theorems for arbitrary
symmetric polyhedra. `PolyhedralNormalForm` now proves the LP conversion and general LP
endpoints using this module. SmallIndexK3Criterion is the sole external mathematical input;
symmetry and approximation are defining data. -/
namespace Lemmata.SpanningTreeSymmetricEF.CoordinateLowerBounds
open scoped BigOperators
open SimpleGraph Approximation ApproximationUpper GraphSubsetBounds HamiltonPath PathLabeling PathCertificate
noncomputable section

/-- Vertex permutations act on actual unordered-edge vectors. -/
def edgeRelabel {N : ℕ} (g : Equiv.Perm (Fin N)) :
    (Sym2 (Fin N) → ℝ) ≃ₗ[ℝ] (Sym2 (Fin N) → ℝ) where
  toFun x e := x (e.map g.symm)
  invFun x e := x (e.map g)
  left_inv x := by
    funext e
    induction e using Sym2.inductionOn with | _ a b => simp
  right_inv x := by
    funext e
    induction e using Sym2.inductionOn with | _ a b => simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical affine action, not an abstract incidence oracle. -/
def edgeAction (N : ℕ) : Equiv.Perm (Fin N) →*
    ((Sym2 (Fin N) → ℝ) ≃ᵃ[ℝ] (Sym2 (Fin N) → ℝ)) where
  toFun g := (edgeRelabel g).toAffineEquiv
  map_one' := by
    ext x e
    induction e using Sym2.inductionOn with | _ a b => rfl
  map_mul' g h := by
    ext x e
    induction e using Sym2.inductionOn with | _ a b => rfl

theorem incidence_equivariant {N : ℕ} (g π : Equiv.Perm (Fin N)) :
    graphIncidence (graph (π * g⁻¹)) = edgeAction N g (graphIncidence (graph π)) := by
  classical
  funext e
  induction e using Sym2.inductionOn with
  | _ a b => rfl

/-- Left action on label-to-position permutations by inverse precomposition. -/
@[reducible] def inverseRelabelAction (N : ℕ) :
    MulAction (Equiv.Perm (Fin N)) (Equiv.Perm (Fin N)) where
  smul g π := π * g⁻¹
  one_smul π := by
    change π * (1 : Equiv.Perm (Fin N))⁻¹ = π
    simp
  mul_smul g h π := by
    change π * (g * h)⁻¹ = (π * h⁻¹) * g⁻¹
    simp [mul_assoc]

variable {E J : Type*} [AddCommGroup E] [Module ℝ E]

/-- Actual feasible extension points: an affine slice and affine slacks. -/
def feasible (Q : AffineSubspace ℝ E) (slack : J → E →ᵃ[ℝ] ℝ) : Set E :=
  {z | z ∈ Q ∧ ∀ j, 0 ≤ slack j z}

theorem feasible_convex (Q : AffineSubspace ℝ E) (slack : J → E →ᵃ[ℝ] ℝ) :
    Convex ℝ (feasible Q slack) := by
  have hh : feasible Q slack = (Q : Set E) ∩ ⋂ j, (slack j) ⁻¹' Set.Ici 0 := by
    ext z
    simp [feasible]
  rw [hh]
  exact Q.convex.inter (convex_iInter (fun j => (convex_Ici (0 : ℝ)).affine_preimage (slack j)))

/-- Nonnegative functions constant on actual alternating orbits have
nonnegative signed expectation. The orbit masses come from PathOrbit. -/
theorem invariant_weighted_sum_nonneg {N : ℕ} (hN : 7 ≤ N)
    (d : Fin 3 ↪ Fin N) (W : Finset (Fin N)) (hW : W.card ≤ 2)
    (f : Equiv.Perm (Fin N) → ℝ) (hf : ∀ π, 0 ≤ f π)
    (hinv : ∀ π ρ, PathOrbit.alternatingOrbit W π ρ → f ρ = f π) :
    0 ≤ ∑ π, weight (cycleGraph N) d π * f π := by
  classical
  let K := (↥W → Fin N) × ℤˣ
  have hpart (k : K) : 0 ≤ ∑ π : Equiv.Perm (Fin N) with orbitKey W π = k,
      weight (cycleGraph N) d π * f π := by
    by_cases hk : ∃ ρ, orbitKey W ρ = k
    · obtain ⟨ρ, rfl⟩ := hk
      have he : (∑ π : Equiv.Perm (Fin N) with orbitKey W π = orbitKey W ρ,
          weight (cycleGraph N) d π * f π) =
          (∑ π : Equiv.Perm (Fin N) with orbitKey W π = orbitKey W ρ,
            weight (cycleGraph N) d π) * f ρ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro π hπ
        rw [hinv ρ π ((orbitKey_eq_iff W ρ π).mp (Finset.mem_filter.mp hπ).2)]
      rw [he]
      apply mul_nonneg _ (hf ρ)
      simpa only [Finset.sum_filter, orbitKey_eq_iff, mass] using
        PathOrbit.alternatingOrbit_nonneg (cycleGraph N) d
          (cycle_degree N (by omega)) (by simpa) W hW ρ
    · have he : (Finset.univ.filter (fun π : Equiv.Perm (Fin N) => orbitKey W π = k)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro π hπ
        exact hk ⟨π, (Finset.mem_filter.mp hπ).2⟩
      rw [he, Finset.sum_empty]
  have he := Finset.sum_fiberwise Finset.univ (orbitKey W)
    (fun π => weight (cycleGraph N) d π * f π)
  rw [← he]
  exact Finset.sum_nonneg (fun k _ => hpart k)

/-- Defining symmetry of a normalized coordinate-slack lift. The slacks are
literally permuted, not merely rescaled. `PolyhedralNormalForm.normalForm_exists`
constructs such a presentation from arbitrary finite affine LP descriptions
and actual affine symmetry, without assuming an action on facets. -/
structure ScalarSymmetry {N : ℕ} [MulAction (Equiv.Perm (Fin N)) J]
    (Q : AffineSubspace ℝ E) (slack : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)) where
  rho : Equiv.Perm (Fin N) →* (E ≃ᵃ[ℝ] E)
  slice : ∀ g z, z ∈ Q → rho g z ∈ Q
  slacks : ∀ g j z, slack (g • j) (rho g z) = slack j z
  projection : ∀ g z, p (rho g z) = edgeAction N g (p z)

namespace ScalarSymmetry
variable {N : ℕ} [MulAction (Equiv.Perm (Fin N)) J]
variable {Q : AffineSubspace ℝ E} {slack : J → E →ᵃ[ℝ] ℝ}
variable {p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)}

theorem feasible_stable (D : ScalarSymmetry Q slack p)
    (g : Equiv.Perm (Fin N)) (z : E) (hz : z ∈ feasible Q slack) :
    D.rho g z ∈ feasible Q slack := by
  refine ⟨D.slice g z hz.1, ?_⟩
  intro j
  have hh := D.slacks g (g⁻¹ • j) z
  rw [smul_inv_smul] at hh
  rw [hh]
  exact hz.2 (g⁻¹ • j)

/-- The section is constructed from actual containment by averaging. -/
theorem exists_section (D : ScalarSymmetry Q slack p)
    (hcontains : ∀ π : Equiv.Perm (Fin N),
      graphIncidence (graph π) ∈ SignedLift.lpImage Q slack p) :
    ∃ s : Equiv.Perm (Fin N) → E,
      (∀ π, s π ∈ feasible Q slack) ∧
      (∀ π, p (s π) = graphIncidence (graph π)) ∧
      ∀ g π, s (π * g⁻¹) = D.rho g (s π) := by
  letI := inverseRelabelAction N
  apply EquivariantSection.exists_equivariant_section D.rho (edgeAction N)
    (feasible Q slack) (feasible_convex Q slack) D.feasible_stable p
    (fun π => graphIncidence (graph π)) D.projection
  · exact incidence_equivariant
  · intro π
    obtain ⟨z, hz, hj, hp⟩ := hcontains π
    exact ⟨z, ⟨hz,hj⟩, hp⟩

/-- Actual signed-point membership, derived from small row stabilizers and
true Hamilton-path orbit masses. Neither is a supplied correctness field. -/
theorem signed_point_mem [Fintype J] (D : ScalarSymmetry Q slack p)
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N)
    (hrows : Fintype.card J < Nat.choose N 3) (d : Fin 3 ↪ Fin N)
    (hcontains : ∀ π : Equiv.Perm (Fin N),
      graphIncidence (graph π) ∈ SignedLift.lpImage Q slack p) :
    signedPoint (weight (cycleGraph N) d) (fun π => graphIncidence (graph π)) ∈
      SignedLift.lpImage Q slack p := by
  classical
  obtain ⟨s, hs, hp, heq⟩ := D.exists_section hcontains
  have hw : ∑ π, weight (cycleGraph N) d π = 1 :=
    weight_total _ d (cycle_degree N (by omega)) (by simpa using (show 6 ≤ N by omega))
  refine ⟨∑ π, weight (cycleGraph N) d π • s π,
    SignedLift.weighted_sum_mem Q s _ (fun π => (hs π).1) hw, ?_, ?_⟩
  · intro j
    rw [SignedLift.map_weighted_sum (slack j) s _ hw]
    simp only [smul_eq_mul]
    have hindex : (MulAction.stabilizer (Equiv.Perm (Fin N)) j).index < Nat.choose N 3 := by
      rw [MulAction.index_stabilizer]
      exact lt_of_le_of_lt (by
        simpa only [Nat.card_eq_fintype_card] using
          Set.ncard_le_card (s := MulAction.orbit (Equiv.Perm (Fin N)) j)) hrows
    obtain ⟨W, hW, hle⟩ :=
      smallIndex.exists_alternating_pointwise_stabilizer hN _ hindex
    apply invariant_weighted_sum_nonneg (by omega) d W hW (fun π => slack j (s π))
      (fun π => (hs π).2 j)
    intro π τ hτ
    obtain ⟨g, hg, hgW, rfl⟩ :=
      (PathOrbit.alternatingOrbit_iff_inverse_relabel W π τ).mp hτ
    have hgmem : g ∈ alternatingPointwiseStabilizer W :=
      ⟨Equiv.Perm.mem_alternatingGroup.mpr hg, hgW⟩
    have hfix : g • j = j := hle hgmem
    rw [heq]
    simpa only [hfix] using D.slacks g j (s π)
  · rw [SignedLift.map_weighted_sum p s _ hw]
    simp_rw [hp]
    ext e
    simp [signedPoint]

end ScalarSymmetry

/-- Approximation lower bound for an ACTUAL coordinate-symmetric affine LP
with fewer than choose(N,3) normalized scalar rows. Apart from defining
symmetry/approximation data, only SmallIndexK3Criterion is conditional.
No signed membership, orbit masses, section, or moment is assumed. -/
theorem scalar_factor_lower {N : ℕ} [Fintype J] [MulAction (Equiv.Perm (Fin N)) J]
    (Q : AffineSubspace ℝ E) (slack : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)) (D : ScalarSymmetry Q slack p)
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N)
    (hrows : Fintype.card J < Nat.choose N 3) (beta : ℝ)
    (happrox : MaxApproximation (treeIncidence (V := Fin N)) (SignedLift.lpImage Q slack p) beta) :
    (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)) ≤ beta := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  let d : Fin 3 ↪ Fin (n + 1) := Fin.castLEEmb (by omega)
  have hcontains (π : Equiv.Perm (Fin (n + 1))) :
      graphIncidence (graph π) ∈ SignedLift.lpImage Q slack p :=
    happrox.contains ⟨graph π, graph_isTree_succ π⟩
  have hm := D.signed_point_mem smallIndex hN hrows d hcontains
  have hopt (T : SpanningTree (Fin (n + 1))) :
      objective (subsetCost (distinguished d)) (treeIncidence T) ≤ 2 := by
    have hh := tree_subset_objective T.property (distinguished d)
      (show (distinguished d).Nonempty from ⟨d 0, by simp⟩)
    norm_num only [card_distinguished, Nat.cast_ofNat] at hh
    exact hh
  have hb := happrox.objective_le _ (subsetCost_nonneg (distinguished d)) 2 hopt _ hm
  rw [objective_signedPoint, weighted_triangle_objective (by omega)] at hb
  have he : 3 * (n : ℝ) / (n + 1) =
      2 * ((3 / 2 : ℝ) * (1 - 1 / (n + 1))) := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [he] at hb
  push_cast
  linarith

/-- Strictly better approximation forces at least choose(N,3) normalized
scalar rows. Equality at the approximation threshold is deliberately excluded. -/
theorem scalar_size_lower {N : ℕ} [Fintype J] [MulAction (Equiv.Perm (Fin N)) J]
    (Q : AffineSubspace ℝ E) (slack : J → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] (Sym2 (Fin N) → ℝ)) (D : ScalarSymmetry Q slack p)
    (smallIndex : SmallIndexK3Criterion) (hN : 13 ≤ N) (beta : ℝ)
    (hbeta : beta < (3 / 2 : ℝ) * (1 - 1 / (N : ℝ)))
    (happrox : MaxApproximation (treeIncidence (V := Fin N)) (SignedLift.lpImage Q slack p) beta) :
    Nat.choose N 3 ≤ Fintype.card J := by
  by_contra h
  exact (not_le_of_gt hbeta) (scalar_factor_lower Q slack p D smallIndex hN
    (Nat.lt_of_not_ge h) beta happrox)

end
end Lemmata.SpanningTreeSymmetricEF.CoordinateLowerBounds
