module

public import Lemmata.SpanningTreeSymmetricEF.HamiltonPath
public import Lemmata.SpanningTreeSymmetricEF.ApproximationUpper

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.OrbitCriterion
open scoped BigOperators
open Approximation ApproximationUpper
noncomputable section
instance treeFintype (N : ℕ) : Fintype (SpanningTree (Fin N)) := Fintype.ofFinite _

/-- Finite maxima show that the convex hull of genuine incidence vectors is
an exact maximization formulation.  This does not assume an optimizer oracle. -/
theorem convexHull_maxApproximation {Tree Edge : Type*}
    [Fintype Tree] [Nonempty Tree] [Fintype Edge] (incidence : Tree → Edge → ℝ) :
    MaxApproximation incidence (convexHull ℝ (Set.range incidence)) 1 := by
  classical
  refine ⟨le_rfl, fun T => subset_convexHull ℝ _ ⟨T, rfl⟩, ?_⟩
  intro c _ x hx
  obtain ⟨T, _, hT⟩ := Finset.exists_max_image Finset.univ
    (fun U => objective c (incidence U)) Finset.univ_nonempty
  let L : (Edge → ℝ) →ₗ[ℝ] ℝ := ∑ e, c e • LinearMap.proj e
  have hL (y : Edge → ℝ) : L y = objective c y := by
    simp [L, objective]
  have hconv : Convex ℝ {y | objective c y ≤ objective c (incidence T)} := by
    simpa only [Set.preimage, Set.mem_Iic, hL] using
      (convex_Iic (objective c (incidence T))).linear_preimage L
  have hbound : convexHull ℝ (Set.range incidence) ⊆
      {y | objective c y ≤ objective c (incidence T)} := by
    apply convexHull_min _ hconv
    rintro _ ⟨U, rfl⟩
    exact hT U (Finset.mem_univ U)
  refine ⟨T, ?_⟩
  rw [one_mul]
  exact hbound hx

/-- An exact extension of the actual tree polytope satisfies factor-one
approximation.  Positivity of N is used solely to produce one actual tree. -/
theorem exact_tree_maxApproximation {N : ℕ} (hN : 0 < N)
    {R : Set (Sym2 (Fin N) → ℝ)}
    (hexact : R = convexHull ℝ (Set.range (treeIncidence (V := Fin N)))) :
    MaxApproximation (treeIncidence (V := Fin N)) R 1 := by
  letI : Nonempty (SpanningTree (Fin N)) :=
    ⟨⟨HamiltonPath.graph 1, HamiltonPath.graph_isTree hN 1⟩⟩
  rw [hexact]
  exact convexHull_maxApproximation treeIncidence

end
end Lemmata.SpanningTreeSymmetricEF.OrbitCriterion
