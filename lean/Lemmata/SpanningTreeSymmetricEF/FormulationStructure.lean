module

/-
  Convexity, vertex-permutation symmetry, and exact constraint indexing of the
  concrete LP/SDP formulations. Equations are not counted; each scalar
  inequality is an order-one block and the SDP has one additional order-|V|
  PSD block. These are formulation sizes, not definitions of minimum extension
  complexity over all possible lifts.
-/
public import Lemmata.SpanningTreeSymmetricEF.ApproximationUpper
public import Lemmata.SpanningTreeSymmetricEF.ApproximationSharpness

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.FormulationStructure

open scoped BigOperators
open SimpleGraph SDPBounds TreeModels ApproximationUpper

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex permutations act by simultaneous row/column reindexing. -/
def permuteMatrix (g : Equiv.Perm V) (M : Matrix V V ℝ) : Matrix V V ℝ :=
  M.submatrix g.symm g.symm

def permuteVector (g : Equiv.Perm V) (x : Sym2 V → ℝ) : Sym2 V → ℝ :=
  fun e => x (Sym2.map g.symm e)

omit [Fintype V] [DecidableEq V] in
theorem projection_permute (g : Equiv.Perm V) (y : Matrix V V ℝ) :
    projection (permuteMatrix g y) = permuteVector g (projection y) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ i j => rfl

omit [DecidableEq V] in
theorem lp_permute {y : Matrix V V ℝ} (h : LPFeasible y) (g : Equiv.Perm V) :
    LPFeasible (permuteMatrix g y) := by
  refine ⟨fun i j => h.nonneg _ _, fun i => h.diagonal _, ?_, fun i j => h.capacity _ _⟩
  intro i
  change (∑ j, y (g.symm i) (g.symm j)) ≤ 1
  rw [g.symm.sum_comp]
  exact h.outdegree _

omit [DecidableEq V] in
theorem sdp_permute {y X : Matrix V V ℝ} (h : Feasible y X) (g : Equiv.Perm V) :
    Feasible (permuteMatrix g y) (permuteMatrix g X) := by
  refine ⟨fun i j => h.nonneg _ _, fun i => h.diagonal_y _, ?_,
    h.psd.submatrix g.symm, fun i => h.diagonal_X _, ?_⟩
  · intro i
    change (∑ j, y (g.symm i) (g.symm j)) ≤ 1
    rw [g.symm.sum_comp]
    exact h.outdegree _
  · intro i j hij
    exact h.cut_bound _ _ (g.symm.injective.ne hij)

omit [DecidableEq V] in
theorem lp_symmetric (g : Equiv.Perm V) {x : Sym2 V → ℝ} (hx : x ∈ lpRelaxation) :
    permuteVector g x ∈ lpRelaxation := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨permuteMatrix g y, lp_permute hy g, projection_permute g y⟩

omit [DecidableEq V] in
theorem sdp_symmetric (g : Equiv.Perm V) {x : Sym2 V → ℝ} (hx : x ∈ sdpRelaxation) :
    permuteVector g x ∈ sdpRelaxation := by
  obtain ⟨y, X, hy, rfl⟩ := hx
  exact ⟨permuteMatrix g y, permuteMatrix g X, sdp_permute hy g, projection_permute g y⟩

omit [Fintype V] [DecidableEq V] in
theorem projection_mix (a b : ℝ) (y z : Matrix V V ℝ) :
    projection (a • y + b • z) = a • projection y + b • projection z := by
  funext e
  induction e using Sym2.inductionOn with
  | _ i j => simp [projection, edgeWeights]; ring

omit [DecidableEq V] in
private theorem row_mix (a b : ℝ) (y z : Matrix V V ℝ) (i : V) :
    (∑ j, (a • y + b • z) i j) = a * (∑ j, y i j) + b * (∑ j, z i j) := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
private theorem edge_mix (a b : ℝ) (y z : Matrix V V ℝ) (i j : V) :
    edgeWeights (a • y + b • z) i j = a * edgeWeights y i j + b * edgeWeights z i j := by
  simp [edgeWeights]
  ring

omit [DecidableEq V] in
theorem lp_mix {y z : Matrix V V ℝ} (hy : LPFeasible y) (hz : LPFeasible z)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    LPFeasible (a • y + b • z) := by
  constructor
  · intro i j
    exact add_nonneg (mul_nonneg ha (hy.nonneg i j)) (mul_nonneg hb (hz.nonneg i j))
  · intro i
    simp [hy.diagonal, hz.diagonal]
  · intro i
    rw [row_mix]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hy.outdegree i) ha)
      (mul_le_mul_of_nonneg_left (hz.outdegree i) hb)
    simpa [hab] using hh
  · intro i j
    rw [edge_mix]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hy.capacity i j) ha)
      (mul_le_mul_of_nonneg_left (hz.capacity i j) hb)
    simpa [hab] using hh

omit [DecidableEq V] in
theorem sdp_mix {y z X Z : Matrix V V ℝ} (hy : Feasible y X) (hz : Feasible z Z)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Feasible (a • y + b • z) (a • X + b • Z) := by
  constructor
  · intro i j
    exact add_nonneg (mul_nonneg ha (hy.nonneg i j)) (mul_nonneg hb (hz.nonneg i j))
  · intro i
    simp [hy.diagonal_y, hz.diagonal_y]
  · intro i
    rw [row_mix]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hy.outdegree i) ha)
      (mul_le_mul_of_nonneg_left (hz.outdegree i) hb)
    simpa [hab] using hh
  · exact (hy.psd.smul ha).add (hz.psd.smul hb)
  · intro i
    simp [hy.diagonal_X, hz.diagonal_X, hab]
  · intro i j hij
    rw [edge_mix]
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hy.cut_bound i j hij) ha)
      (mul_le_mul_of_nonneg_left (hz.cut_bound i j hij) hb)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    nlinarith

omit [DecidableEq V] in
theorem lp_convex : Convex ℝ (lpRelaxation (V := V)) := by
  intro x hx z hz a b ha hb hab
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨a • y + b • w, lp_mix hy hw ha hb hab, projection_mix a b y w⟩

omit [DecidableEq V] in
theorem sdp_convex : Convex ℝ (sdpRelaxation (V := V)) := by
  intro x hx z hz a b ha hb hab
  obtain ⟨y, X, hy, rfl⟩ := hx
  obtain ⟨w, W, hw, rfl⟩ := hz
  exact ⟨a • y + b • w, a • X + b • W, sdp_mix hy hw ha hb hab, projection_mix a b y w⟩

/-- Containment of the entire spanning-tree polytope, not just its vertices. -/
theorem tree_polytope_subset_lp [Nonempty V] :
    convexHull ℝ (Set.range (treeIncidence (V := V))) ⊆ lpRelaxation := by
  apply convexHull_min _ lp_convex
  rintro x ⟨T, rfl⟩
  exact lp_three_halves.contains T

theorem tree_polytope_subset_sdp [Nonempty V] :
    convexHull ℝ (Set.range (treeIncidence (V := V))) ⊆ sdpRelaxation := by
  apply convexHull_min _ sdp_convex
  rintro x ⟨T, rfl⟩
  exact sdp_four_thirds.contains T

omit [DecidableEq V] in
/-- The optional total-cardinality equation is an affine slice; convexity and
containment of the entire tree polytope are retained, not just vertex containment. -/
theorem cardinalitySlice_convex {R : Set (Sym2 V → ℝ)} (hR : Convex ℝ R) :
    Convex ℝ (ApproximationSharpness.cardinalitySlice R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hR hx.1 hy.1 ha hb hab, ?_⟩
  change (∑ e, (a * x e + b * y e)) = _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
  rw [← add_mul, hab, one_mul]

theorem tree_polytope_subset_lp_cardinality [Nonempty V] :
    convexHull ℝ (Set.range (treeIncidence (V := V))) ⊆
      ApproximationSharpness.cardinalitySlice lpRelaxation := by
  apply convexHull_min _ (cardinalitySlice_convex lp_convex)
  rintro x ⟨T, rfl⟩
  exact (ApproximationSharpness.approximation_cardinalitySlice lp_three_halves).contains T

theorem tree_polytope_subset_sdp_cardinality [Nonempty V] :
    convexHull ℝ (Set.range (treeIncidence (V := V))) ⊆
      ApproximationSharpness.cardinalitySlice sdpRelaxation := by
  apply convexHull_min _ (cardinalitySlice_convex sdp_convex)
  rintro x ⟨T, rfl⟩
  exact (ApproximationSharpness.approximation_cardinalitySlice sdp_four_thirds).contains T

abbrev Arc (V : Type*) := {p : V × V // p.1 ≠ p.2}
abbrev Edge (V : Type*) := {e : Sym2 V // ¬e.IsDiag}
abbrev ScalarConstraint (V : Type*) := Arc V ⊕ (Edge V ⊕ V)

theorem card_arcs : Fintype.card (Arc V) = 2 * (Fintype.card V).choose 2 := by
  classical
  have hc : Fintype.card (Arc V) = ((Finset.univ : Finset V).offDiag).card := by
    have e : Arc V ≃ ((Finset.univ : Finset V).offDiag : Finset (V × V)) :=
      Equiv.subtypeEquivRight (fun p => by simp)
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  rw [hc, ← Sym2.two_mul_card_image_offDiag, Sym2.card_image_offDiag]
  simp

theorem card_edges : Fintype.card (Edge V) = (Fintype.card V).choose 2 :=
  Sym2.card_subtype_not_diag

/-- Both formulations have these actual scalar inequality indices. -/
theorem scalar_constraint_count :
    Fintype.card (ScalarConstraint V) = 3 * (Fintype.card V).choose 2 + Fintype.card V := by
  simp only [ScalarConstraint, Fintype.card_sum, card_arcs, card_edges]
  omega

/-- SDP size is the scalar count plus the order of its single PSD block. -/
theorem sdp_formulation_size :
    Fintype.card (ScalarConstraint V) + Fintype.card V =
      3 * (Fintype.card V).choose 2 + 2 * Fintype.card V := by
  rw [scalar_constraint_count]
  omega

def lpSlack (y : Matrix V V ℝ) : ScalarConstraint V → ℝ
  | .inl p => y p.val.1 p.val.2
  | .inr (.inl e) => 1 - projection y e.val
  | .inr (.inr i) => 1 - ∑ j, y i j

/-- A symmetric expression agrees with (1-X_ij)/2 on PSD real matrices. -/
def cutProjection (X : Matrix V V ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => (2 - X i j - X j i) / 4, by intro i j; ring⟩

def sdpSlack (y X : Matrix V V ℝ) : ScalarConstraint V → ℝ
  | .inl p => y p.val.1 p.val.2
  | .inr (.inl e) => cutProjection X e.val - projection y e.val
  | .inr (.inr i) => 1 - ∑ j, y i j

/-- Removes only duplicate/diagonal scalar inequalities; equations are kept separate. -/
theorem lp_indexed_constraints (y : Matrix V V ℝ) :
    LPFeasible y ↔ (∀ i, y i i = 0) ∧ ∀ q, 0 ≤ lpSlack y q := by
  constructor
  · intro h
    refine ⟨h.diagonal, ?_⟩
    rintro (p | e | i)
    · exact h.nonneg _ _
    · rcases e with ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ i j => exact sub_nonneg.mpr (h.capacity i j)
    · exact sub_nonneg.mpr (h.outdegree i)
  · rintro ⟨hd, hs⟩
    refine ⟨?_, hd, ?_, ?_⟩
    · intro i j
      by_cases hij : i = j
      · subst j; simp [hd]
      · exact hs (.inl ⟨(i,j), hij⟩)
    · intro i
      exact sub_nonneg.mp (hs (.inr (.inr i)))
    · intro i j
      by_cases hij : i = j
      · subst j; simp [edgeWeights, hd]
      · exact sub_nonneg.mp (hs (.inr (.inl ⟨s(i,j), by simpa using hij⟩)))

/-- Exactly the scalar/PSD constraints of the SDP, with the claimed index count. -/
theorem sdp_indexed_constraints (y X : Matrix V V ℝ) :
    Feasible y X ↔ (∀ i, y i i = 0) ∧ X.PosSemidef ∧ (∀ i, X i i = 1) ∧
      ∀ q, 0 ≤ sdpSlack y X q := by
  constructor
  · intro h
    refine ⟨h.diagonal_y, h.psd, h.diagonal_X, ?_⟩
    rintro (p | e | i)
    · exact h.nonneg _ _
    · rcases e with ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ i j =>
        have hij : i ≠ j := by simpa using he
        have hh := h.cut_bound i j hij
        have hsym : X j i = X i j := by simpa using h.psd.isHermitian.apply i j
        change 0 ≤ (2 - X i j - X j i) / 4 - edgeWeights y i j
        rw [hsym]
        linarith
    · exact sub_nonneg.mpr (h.outdegree i)
  · rintro ⟨hd, hX, hdX, hs⟩
    refine ⟨?_, hd, ?_, hX, hdX, ?_⟩
    · intro i j
      by_cases hij : i = j
      · subst j; simp [hd]
      · exact hs (.inl ⟨(i,j), hij⟩)
    · intro i
      exact sub_nonneg.mp (hs (.inr (.inr i)))
    · intro i j hij
      have hh := hs (.inr (.inl ⟨s(i,j), by simpa using hij⟩))
      have hsym : X j i = X i j := by simpa using hX.isHermitian.apply i j
      change 0 ≤ (2 - X i j - X j i) / 4 - edgeWeights y i j at hh
      rw [hsym] at hh
      linarith

end
end Lemmata.SpanningTreeSymmetricEF.FormulationStructure
