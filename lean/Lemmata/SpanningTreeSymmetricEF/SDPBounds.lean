module

/-
  Matrix and subset inequalities for the 4/3 spanning-tree SDP.

  These are actual finite-matrix statements, not an assumed SDP correctness
  interface. The identification of the forest inequality system with the convex
  hull of forests (Edmonds' theorem), and extension of a forest to a spanning
  tree, remain outside this module. Consequently the approximation guarantee
  for all nonnegative objectives is not yet an end-to-end Lean theorem.
-/
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.SDPBounds

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The undirected edge vector, extended by zero on the diagonal when the
orientation variables have zero diagonal. -/
def edgeWeights (y : Matrix V V ℝ) : Matrix V V ℝ :=
  fun i j => y i j + y j i

/-- Sum over unordered internal edges, expressed without a choice of order on V. -/
def internalWeight (x : Matrix V V ℝ) (U : Finset V) : ℝ :=
  (∑ i ∈ U, ∑ j ∈ U, x i j) / 2

/-- Exactly the matrix/orientation constraints of the paper's SDP. Diagonal
orientation variables are added as zeros, not as extra inequalities. -/
structure Feasible (y X : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ y i j
  diagonal_y : ∀ i, y i i = 0
  outdegree : ∀ i, ∑ j, y i j ≤ 1
  psd : X.PosSemidef
  diagonal_X : ∀ i, X i i = 1
  cut_bound : ∀ i j, i ≠ j → edgeWeights y i j ≤ (1 - X i j) / 2

omit [Fintype V] [DecidableEq V] in
theorem internalWeight_edgeWeights (y : Matrix V V ℝ) (U : Finset V) :
    internalWeight (edgeWeights y) U = ∑ i ∈ U, ∑ j ∈ U, y i j := by
  unfold internalWeight edgeWeights
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => y j i)]
  ring

omit [DecidableEq V] in
theorem Feasible.internalWeight_le_card {y X : Matrix V V ℝ}
    (h : Feasible y X) (U : Finset V) :
    internalWeight (edgeWeights y) U ≤ (U.card : ℝ) := by
  rw [internalWeight_edgeWeights]
  calc
    _ ≤ ∑ i ∈ U, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.sum_le_univ_sum_of_nonneg (s := U) (fun j => h.nonneg i j)).trans
        (h.outdegree i)
    _ = _ := by simp

omit [Fintype V] [DecidableEq V] in
/-- PSD positivity tested on the indicator of a finite subset. -/
theorem psd_subset_sum_nonnegative {X : Matrix V V ℝ} (hX : X.PosSemidef)
    (U : Finset V) : 0 ≤ ∑ i ∈ U, ∑ j ∈ U, X i j := by
  have h := (hX.submatrix (fun i : U => (i : V))).dotProduct_mulVec_nonneg
    (fun _ => (1 : ℝ))
  have h' : 0 ≤ ∑ i ∈ U.attach, ∑ j ∈ U, X (i : V) j := by
    simpa [dotProduct, Matrix.mulVec, Matrix.submatrix, Finset.sum_coe_sort,
      Finset.sum_attach] using h
  simpa only [Finset.sum_attach U (fun i => ∑ j ∈ U, X i j)] using h'

/-- The cut-matrix bound for every subset, not only triangles. -/
theorem Feasible.internalWeight_le_card_sq_div_four {y X : Matrix V V ℝ}
    (h : Feasible y X) (U : Finset V) :
    internalWeight (edgeWeights y) U ≤ (U.card : ℝ)^2 / 4 := by
  have hcut : ∀ i j, edgeWeights y i j ≤ (1 - X i j) / 2 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [edgeWeights, h.diagonal_y, h.diagonal_X]
    · exact h.cut_bound i j hij
  have hsum : (∑ i ∈ U, ∑ j ∈ U, edgeWeights y i j) ≤
      ∑ i ∈ U, ∑ j ∈ U, (1 - X i j) / 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcut i j
  have hrhs : (∑ i ∈ U, ∑ j ∈ U, (1 - X i j) / 2) =
      ((U.card : ℝ)^2 - ∑ i ∈ U, ∑ j ∈ U, X i j) / 2 := by
    simp_rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [pow_two]
  rw [hrhs] at hsum
  have hpos := psd_subset_sum_nonnegative h.psd U
  unfold internalWeight
  linarith

/-- The triangle inequality used in the paper's SDP upper-bound proof. -/
theorem Feasible.triangle_bound {y X : Matrix V V ℝ}
    (h : Feasible y X) (U : Finset V) (hU : U.card = 3) :
    internalWeight (edgeWeights y) U ≤ (9 / 4 : ℝ) := by
  have hh := h.internalWeight_le_card_sq_div_four U
  norm_num [hU] at hh
  exact hh

/-- Every SDP-feasible point, after scaling by 3/4, satisfies every nonempty
forest subset inequality. This does not assume Edmonds' polytope theorem. -/
theorem Feasible.scaled_forest_inequality {y X : Matrix V V ℝ}
    (h : Feasible y X) (U : Finset V) (hU : U.Nonempty) :
    (3 / 4 : ℝ) * internalWeight (edgeWeights y) U ≤ (U.card : ℝ) - 1 := by
  have hcard : 1 ≤ U.card := hU.card_pos
  by_cases h1 : U.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
    simp [internalWeight, edgeWeights, h.diagonal_y]
  by_cases h2 : U.card = 2
  · have hh := h.internalWeight_le_card_sq_div_four U
    norm_num [h2] at hh ⊢
    linarith
  by_cases h3 : U.card = 3
  · have hh := h.triangle_bound U h3
    norm_num [h3]
    linarith
  have h4 : (4 : ℝ) ≤ U.card := by exact_mod_cast (by omega : 4 ≤ U.card)
  have hh := h.internalWeight_le_card U
  linarith

omit [Fintype V] [DecidableEq V] in
/-- The signed block sum used by the retained block-size proposition. The
partition must be supplied for the actual matrix-valued function and weights;
its construction from group stabilizers is not asserted here. -/
theorem signed_block_sum_posSemidef {Point Block : Type*}
    [Fintype Point] [Fintype Block] [DecidableEq Block]
    (blockOf : Point → Block) (w : Point → ℝ) (A : Block → Matrix V V ℝ)
    (hA : ∀ b, (A b).PosSemidef)
    (hmass : ∀ b, 0 ≤ ∑ t : Point with blockOf t = b, w t) :
    (∑ t, w t • A (blockOf t)).PosSemidef := by
  have hid : (∑ b : Block, (∑ t : Point with blockOf t = b, w t) • A b) =
      ∑ t, w t • A (blockOf t) := by
    simp_rw [Finset.sum_smul]
    calc
      _ = ∑ b : Block, ∑ t : Point with blockOf t = b, w t • A (blockOf t) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := Finset.sum_fiberwise Finset.univ blockOf (fun t => w t • A (blockOf t))
  rw [← hid]
  exact Matrix.posSemidef_sum Finset.univ fun b _ => (hA b).smul (hmass b)

end
end Lemmata.SpanningTreeSymmetricEF.SDPBounds
