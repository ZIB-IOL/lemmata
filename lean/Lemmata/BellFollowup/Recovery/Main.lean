module

public import Lemmata.BellFollowup.Recovery.Geometry
public import Lemmata.BellFollowup.Recovery.Energy

@[expose] public section

/-!
# Cross-polytope recovery from one-party estimates

This is the convex-geometric part of the all-settings Bell theorem. Its inputs
are named explicitly so they can be discharged by any separate formalization
of the signed shifts, projection and frequency polygons.
-/

namespace Lemmata.BellFollowup.Recovery

open scoped BigOperators

/-- Recovery for an entire atom set. The input for each atom is a collection
of nonnegative amplitudes, one per party and mode. The phase adjustment is a
single upper bound C, which may be chosen as sqrt 2, or as 1 in the odd case. -/
theorem convexHull_recovery_of_energy
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Type*) [Fintype P]
    (V : Matrix ι ι ℝ) (A : Set (ι → ℝ)) {m C : ℝ}
    (hm : 2 ≤ m) (hd : (Fintype.card ι : ℝ) ≤ m) (hC : 0 ≤ C)
    (hcut : C ^ 2 * (5 / 8 : ℝ) ^ Fintype.card P ≤ 1 / (4 * m ^ 3))
    (hdiag : ∀ i, V i i = 1)
    (hcols : V.mulVecLin '' CrossHull.signedAxes ι ⊆ A)
    (hgap : ∀ x ∈ A, x ∉ V.mulVecLin '' CrossHull.signedAxes ι →
      ∀ i, |x i| ≤ 1 - 1 / m ^ 2)
    (henergy : ∀ x ∈ A, ∃ a : P → ι → ℝ,
      (∀ p i, 0 ≤ a p i) ∧ (∀ p, ∑ i, a p i ^ 2 ≤ (5 : ℝ)/4) ∧
      ∀ i, |x i| ≤ C * ∏ p, a p i) :
    Function.Bijective V.mulVecLin ∧
      convexHull ℝ A = V.mulVecLin '' {z : ι → ℝ | mass z ≤ 1} := by
  classical
  let t : ℝ := C ^ 2 * (5 / 8 : ℝ) ^ Fintype.card P
  have hp : ∀ x ∈ A, ∀ i j, i ≠ j → |x i| * |x j| ≤ t := by
    intro x hx i j hij
    obtain ⟨a, hn, he, h⟩ := henergy x hx
    exact pair_decay_of_energy a hn he x hC h hij
  have hc (j : ι) : (fun i => V i j) ∈ A := by
    apply hcols
    refine ⟨CrossHull.axis j 1, ⟨j, Or.inl rfl⟩, ?_⟩
    funext i
    change (∑ l, V i l * (if j = l then (1 : ℝ) else 0)) = V i j
    simp [mul_ite]
  have ho (i j : ι) (hij : i ≠ j) : |V i j| ≤ t := by
    simpa [hdiag] using hp _ (hc j) i j hij
  exact convexHull_recovery V A hm hd (by positivity) hcut hdiag ho hcols hgap hp

end Lemmata.BellFollowup.Recovery
