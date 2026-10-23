module

/-
  Actual signed points in affine orthant/product-PSD lifts.

  These lemmas prove membership from an actual section and actual partition
  values; membership is a conclusion, not a hypothesis. Construction of an
  equivariant section and its partitions from a small symmetric extension is
  a distinct group/geometric reduction and is not assumed proved here.
-/
public import Lemmata.SpanningTreeSymmetricEF.SDPBounds

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.SignedLift

open scoped BigOperators

noncomputable section
variable {Point E F : Type*} [Fintype Point]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Signed affine combinations, not only convex combinations, preserve the
actual affine equations when their total weight is one. -/
theorem weighted_sum_mem (Q : AffineSubspace ℝ E) (s : Point → E) (w : Point → ℝ)
    (hs : ∀ t, s t ∈ Q) (hw : ∑ t, w t = 1) : (∑ t, w t • s t) ∈ Q := by
  have hw' : ∑ t ∈ (Finset.univ : Finset Point), w t = 1 := by simpa using hw
  have hspan : affineSpan ℝ (Set.range s) ≤ Q := affineSpan_le.mpr (by
    rintro _ ⟨t, rfl⟩
    exact hs t)
  have hh := hspan (affineCombination_mem_affineSpan hw' s)
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw'] using hh

/-- Affine projection of the same signed section uses the same weights. -/
theorem map_weighted_sum (p : E →ᵃ[ℝ] F) (s : Point → E) (w : Point → ℝ)
    (hw : ∑ t, w t = 1) : p (∑ t, w t • s t) = ∑ t, w t • p (s t) := by
  have hw' : ∑ t ∈ (Finset.univ : Finset Point), w t = 1 := by simpa using hw
  have hh := Finset.univ.map_affineCombination s w hw' p
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw',
    Function.comp_apply] using hh

variable {Constraint : Type*}

/-- A concrete affine slice with scalar inequalities, projected by an affine map. -/
def lpImage (Q : AffineSubspace ℝ E) (slack : Constraint → E →ᵃ[ℝ] ℝ)
    (p : E →ᵃ[ℝ] F) : Set F :=
  {x | ∃ z ∈ Q, (∀ j, 0 ≤ slack j z) ∧ p z = x}

/-- Orthant-lift membership from actual partition-constant section slacks. -/
theorem signed_point_mem_lpImage
    (Q : AffineSubspace ℝ E) (slack : Constraint → E →ᵃ[ℝ] ℝ) (p : E →ᵃ[ℝ] F)
    (s : Point → E) (w : Point → ℝ) (hs : ∀ t, s t ∈ Q) (hw : ∑ t, w t = 1)
    (Part : Constraint → Type*) [∀ j, Fintype (Part j)] [∀ j, DecidableEq (Part j)]
    (blockOf : ∀ j, Point → Part j) (value : ∀ j, Part j → ℝ)
    (hvalue : ∀ j b, 0 ≤ value j b)
    (hsection : ∀ j t, slack j (s t) = value j (blockOf j t))
    (hmass : ∀ j b, 0 ≤ ∑ t : Point with blockOf j t = b, w t) :
    (∑ t, w t • p (s t)) ∈ lpImage Q slack p := by
  refine ⟨∑ t, w t • s t, weighted_sum_mem Q s w hs hw, ?_, map_weighted_sum p s w hw⟩
  intro j
  rw [map_weighted_sum (slack j) s w hw]
  simp_rw [hsection, smul_eq_mul]
  have hid : (∑ b : Part j, (∑ t : Point with blockOf j t = b, w t) * value j b) =
      ∑ t, w t * value j (blockOf j t) := by
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ b : Part j, ∑ t : Point with blockOf j t = b, w t * value j (blockOf j t) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (blockOf j) (fun t => w t * value j (blockOf j t))
  rw [← hid]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (hmass j b) (hvalue j b))

variable {Block : Type*} {Coord : Block → Type*}

/-- General affine matrix constraints; arbitrary additional extension variables
and affine equations are allowed in E and Q. -/
def psdImage (Q : AffineSubspace ℝ E)
    (M : ∀ b, E →ᵃ[ℝ] Matrix (Coord b) (Coord b) ℝ) (p : E →ᵃ[ℝ] F) : Set F :=
  {x | ∃ z ∈ Q, (∀ b, (M b z).PosSemidef) ∧ p z = x}

/-- Product-PSD lift membership from partition masses, with no asserted
correctness field or assumed signed-point membership. -/
theorem signed_point_mem_psdImage
    (Q : AffineSubspace ℝ E) (M : ∀ b, E →ᵃ[ℝ] Matrix (Coord b) (Coord b) ℝ)
    (p : E →ᵃ[ℝ] F) (s : Point → E) (w : Point → ℝ)
    (hs : ∀ t, s t ∈ Q) (hw : ∑ t, w t = 1)
    (Part : Block → Type*) [∀ b, Fintype (Part b)] [∀ b, DecidableEq (Part b)]
    (blockOf : ∀ b, Point → Part b)
    (A : ∀ b, Part b → Matrix (Coord b) (Coord b) ℝ)
    (hA : ∀ b q, (A b q).PosSemidef)
    (hsection : ∀ b t, M b (s t) = A b (blockOf b t))
    (hmass : ∀ b q, 0 ≤ ∑ t : Point with blockOf b t = q, w t) :
    (∑ t, w t • p (s t)) ∈ psdImage Q M p := by
  refine ⟨∑ t, w t • s t, weighted_sum_mem Q s w hs hw, ?_, map_weighted_sum p s w hw⟩
  intro b
  rw [map_weighted_sum (M b) s w hw]
  simp_rw [hsection]
  exact SDPBounds.signed_block_sum_posSemidef (blockOf b) w (A b) (hA b) (hmass b)

end
end Lemmata.SpanningTreeSymmetricEF.SignedLift
