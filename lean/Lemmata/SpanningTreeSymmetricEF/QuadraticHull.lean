module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticAlgebra
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology

@[expose] public section


/-! Exact convex-hull membership from the forest inequalities and cardinality.
Uses the previously proved weighted forest theorem and finite-dimensional
separation. Edmonds' convex-hull conclusion is not an assumed interface. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticHull
open scoped BigOperators
open SimpleGraph ApproximationUpper ApproximationSharpness
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem all_objective_dominance (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ e, e.IsDiag → x e = 0)
    (hs : ∀ S : Finset V, S.Nonempty → (∑ e ∈ S.sym2, x e) ≤ (S.card : ℝ) - 1)
    (hm : ∑ e, x e = (Fintype.card V : ℝ) - 1) (c : Sym2 V → ℝ) :
    ∃ T : SpanningTree V, (∑ e, c e * x e) ≤ ∑ e, c e * treeIncidence T e := by
  classical
  let C : ℝ := ∑ e, |c e|
  have hc (e : Sym2 V) : 0 ≤ c e + C := by
    have hle : |c e| ≤ C := Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ e)
    have hlo := neg_abs_le (c e)
    linarith
  letI : DecidableRel (⊤ : SimpleGraph V).Adj := Classical.decRel _
  obtain ⟨T,hT,_,hw⟩ := ForestPolytope.weighted_spanning_tree_dominance x hx hd hs
    (⊤ : SimpleGraph V) connected_top (fun e => c e + C) hc
  rw [sum_top_edges_eq_sum _ (by intro e he; rw [hd e he, mul_zero]),
    ← objective_graphIncidence] at hw
  have hmass := tree_mass hT
  have hsplit (z : Sym2 V → ℝ) :
      (∑ e, (c e + C) * z e) = (∑ e, c e * z e) + C * ∑ e, z e := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  change (∑ e, (c e + C) * x e) ≤ ∑ e, (c e + C) * graphIncidence T e at hw
  rw [hsplit x, hsplit (graphIncidence T), hm, hmass] at hw
  exact ⟨⟨T,hT⟩, by simpa [treeIncidence] using (add_le_add_iff_right _).mp hw⟩

/-- The exact spanning-tree convex hull, including arbitrary signed objectives. -/
theorem mem_tree_polytope (x : Sym2 V → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ e, e.IsDiag → x e = 0)
    (hs : ∀ S : Finset V, S.Nonempty → (∑ e ∈ S.sym2, x e) ≤ (S.card : ℝ) - 1)
    (hm : ∑ e, x e = (Fintype.card V : ℝ) - 1) :
    x ∈ convexHull ℝ (Set.range (treeIncidence (V := V))) := by
  classical
  by_contra hnot
  have hfinite : (Set.range (treeIncidence (V := V))).Finite := Set.finite_range _
  obtain ⟨f,t,ht,hx'⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (hfinite.isCompact_convexHull ℝ).isClosed hnot
  let c : Sym2 V → ℝ := fun e => f (Pi.single e 1)
  have hf (z : Sym2 V → ℝ) : f z = ∑ e, c e * z e := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    have he : Pi.single e (z e) = z e • Pi.single e (1 : ℝ) := by
      ext i
      by_cases hi : i = e <;> simp [Pi.single_apply, hi]
    rw [he, map_smul]
    simp [c, mul_comm]
  obtain ⟨T,hT⟩ := all_objective_dominance x hx hd hs hm c
  have ht' := ht (treeIncidence T) (subset_convexHull ℝ _ ⟨T,rfl⟩)
  rw [hf] at hx' ht'
  linarith

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticHull
