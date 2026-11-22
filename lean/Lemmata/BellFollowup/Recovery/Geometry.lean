module

public import Lemmata.BellFollowup.Recovery.Recovery
public import Lemmata.BellFollowup.Recovery.CrossHull

@[expose] public section

/-!
# Convex-hull recovery from harmonic coordinate estimates

This statement uses matrix columns and a set of atoms. No initial linear
independence or description of the atom hull is assumed.
-/

namespace Lemmata.BellFollowup.Recovery

open scoped BigOperators

/-- The matrix is invertible and the convex hull of all atoms is exactly its
image of the coordinate cross-polytope. The gap only applies to atoms that
are not themselves signed columns. -/
theorem convexHull_recovery [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (V : Matrix ι ι ℝ) (A : Set (ι → ℝ)) {m t : ℝ}
    (hm : 2 ≤ m) (hd : (Fintype.card ι : ℝ) ≤ m) (ht : 0 ≤ t)
    (hcut : t ≤ 1 / (4 * m ^ 3))
    (hdiag : ∀ i, V i i = 1)
    (hoff : ∀ i j, i ≠ j → |V i j| ≤ t)
    (hcols : V.mulVecLin '' CrossHull.signedAxes ι ⊆ A)
    (hgap : ∀ x ∈ A, x ∉ V.mulVecLin '' CrossHull.signedAxes ι →
      ∀ i, |x i| ≤ 1 - 1 / m ^ 2)
    (hpair : ∀ x ∈ A, ∀ i j, i ≠ j → |x i| * |x j| ≤ t) :
    Function.Bijective V.mulVecLin ∧
      convexHull ℝ A = V.mulVecLin '' {z : ι → ℝ | mass z ≤ 1} := by
  classical
  let E : Matrix ι ι ℝ := V - 1
  have hE (i j : ι) : |E i j| ≤ t := by
    by_cases hij : i = j
    · subst j
      simpa [E, Matrix.one_apply, hdiag] using ht
    · simpa [E, Matrix.one_apply, hij] using hoff i j hij
  have hV (z : ι → ℝ) (i : ι) : V.mulVecLin z i = z i + ∑ j, E i j * z j := by
    change (∑ j, V i j * z j) = z i + ∑ j, (V i j - (1 : Matrix ι ι ℝ) i j) * z j
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hid : (∑ j, (1 : Matrix ι ι ℝ) i j * z j) = z i := by
      change (1 : Matrix ι ι ℝ).mulVec z i = z i
      rw [Matrix.one_mulVec]
    rw [hid]
    ring
  have hpos : 0 < m := by linarith
  have hmt : m * t < 1 := calc
    m * t ≤ m * (1 / (4 * m ^ 3)) := mul_le_mul_of_nonneg_left hcut hpos.le
    _ = 1 / (4 * m ^ 2) := by field_simp
    _ < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < 4 * m ^ 2)).2
      nlinarith [sq_nonneg (m - 2)]
  have hinj := injective_of_mass_lower_bound V.mulVecLin (by linarith : 0 < 1 - m*t)
    (mass_lower_bound V.mulVecLin E hd ht hE hV)
  refine ⟨⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩, ?_⟩
  have hshape : V.mulVecLin '' {z : ι → ℝ | mass z ≤ 1} =
      convexHull ℝ (V.mulVecLin '' CrossHull.signedAxes ι) := by
    rw [← LinearMap.image_convexHull, CrossHull.convexHull_signedAxes]
    rfl
  rw [hshape]
  apply Set.Subset.antisymm _ (convexHull_mono hcols)
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  by_cases hc : x ∈ V.mulVecLin '' CrossHull.signedAxes ι
  · exact subset_convexHull ℝ _ hc
  · obtain ⟨z, hz, _⟩ := recovery_of_pair_decay V.mulVecLin E hm hd ht hcut hE hV x
      (hgap x hx hc) (hpair x hx)
    rw [← hshape]
    exact ⟨z, hz.2.le, hz.1⟩

end Lemmata.BellFollowup.Recovery
