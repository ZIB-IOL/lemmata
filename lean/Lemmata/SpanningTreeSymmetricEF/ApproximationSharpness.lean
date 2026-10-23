module

public import Lemmata.SpanningTreeSymmetricEF.GraphSubsetBounds
public import Lemmata.SpanningTreeSymmetricEF.ApproximationChecks

@[expose] public section


/-! Genuine LP/SDP gap witnesses on a distinguished cycle and arbitrary extra vertices. -/
namespace Lemmata.SpanningTreeSymmetricEF.ApproximationSharpness
open scoped BigOperators
open SimpleGraph SDPBounds TreeModels ApproximationUpper ApproximationChecks
open Approximation GraphSubsetBounds
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Disjoint union of arc matrices, with all cross arcs zero. -/
def sumArcs (y : Matrix A A ℝ) (z : Matrix B B ℝ) : Matrix (A ⊕ B) (A ⊕ B) ℝ :=
  Matrix.fromBlocks y 0 0 z

omit [DecidableEq A] [DecidableEq B] in
theorem lp_sum {y : Matrix A A ℝ} {z : Matrix B B ℝ}
    (hy : LPFeasible y) (hz : LPFeasible z) : LPFeasible (sumArcs y z) := by
  constructor
  · rintro (i | i) (j | j) <;> simp [sumArcs, hy.nonneg, hz.nonneg]
  · rintro (i | i) <;> simp [sumArcs, hy.diagonal, hz.diagonal]
  · rintro (i | i)
    · simpa [sumArcs, Fintype.sum_sum_type] using hy.outdegree i
    · simpa [sumArcs, Fintype.sum_sum_type] using hz.outdegree i
  · rintro (i | i) (j | j)
    · exact hy.capacity i j
    · norm_num [sumArcs, edgeWeights]
    · norm_num [sumArcs, edgeWeights]
    · exact hz.capacity i j

omit [DecidableEq B] in
/-- Zero arcs are valid for arbitrary background vertices, including the empty type. -/
theorem lp_zero : LPFeasible (0 : Matrix B B ℝ) := by
  constructor <;> intros <;> simp [edgeWeights]

theorem triangle_lp_feasible : LPFeasible triangleY := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [triangleY]
  · intro i; fin_cases i <;> norm_num [triangleY]
  · intro i; fin_cases i <;> norm_num [triangleY, Fin.sum_univ_succ]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [triangleY, edgeWeights]

/-- The distinguished vertex subset is the whole left summand. -/
def leftVertices : Finset (A ⊕ B) := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem card_leftVertices : (leftVertices (A := A) (B := B)).card = Fintype.card A := by
  simp [leftVertices]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem leftVertices_nonempty [Nonempty A] : (leftVertices (A := A) (B := B)).Nonempty := by
  simp [leftVertices]

theorem objective_left (y : Matrix A A ℝ) (z : Matrix B B ℝ) (hd : ∀ i, y i i = 0)
    (hzd : ∀ i, z i i = 0) :
    objective (subsetCost (leftVertices (A := A) (B := B))) (projection (sumArcs y z)) =
      internalWeight (edgeWeights y) Finset.univ := by
  rw [objective_subsetCost, projection_subset_sum]
  · simp [internalWeight, leftVertices, sumArcs, edgeWeights]
  · rintro (i | i) <;> simp [sumArcs, hd, hzd]

/-- The background can be arbitrary; the triangle objective remains exactly three. -/
theorem lp_witness {z : Matrix B B ℝ} (hz : LPFeasible z) :
    LPFeasible (sumArcs triangleY z) ∧
    objective (subsetCost (leftVertices (A := Fin 3) (B := B)))
      (projection (sumArcs triangleY z)) = 3 := by
  refine ⟨lp_sum triangle_lp_feasible hz, ?_⟩
  rw [objective_left _ _ triangle_lp_feasible.diagonal hz.diagonal]
  norm_num [internalWeight, edgeWeights, triangleY, Fin.sum_univ_succ]

/-- No smaller factor works on Fin 3 plus any finite set of extra vertices. -/
theorem lp_factor_ge_three_halves {beta : ℝ}
    (h : MaxApproximation (treeIncidence (V := Fin 3 ⊕ B)) lpRelaxation beta) :
    (3 / 2 : ℝ) ≤ beta := by
  let U := leftVertices (A := Fin 3) (B := B)
  obtain ⟨hf, hv⟩ := lp_witness (lp_zero (B := B))
  have hh := h.objective_le (subsetCost U) (subsetCost_nonneg U) 2
    (fun T => by
      have ht := tree_subset_objective T.property U leftVertices_nonempty
      norm_num [U] at ht
      exact ht)
    (projection (sumArcs triangleY (0 : Matrix B B ℝ))) ⟨_, hf, rfl⟩
  rw [hv] at hh
  linarith

omit [DecidableEq A] [DecidableEq B] in
/-- Positive semidefiniteness of the disjoint block sum, proved on quadratic forms. -/
theorem psd_sum {X : Matrix A A ℝ} {Z : Matrix B B ℝ}
    (hX : X.PosSemidef) (hZ : Z.PosSemidef) : (sumArcs X Z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro (i | i) (j | j)
    · exact hX.isHermitian.apply i j
    · simp [sumArcs]
    · simp [sumArcs]
    · exact hZ.isHermitian.apply i j
  · intro v
    have hx := hX.dotProduct_mulVec_nonneg (fun i => v (.inl i))
    have hz := hZ.dotProduct_mulVec_nonneg (fun i => v (.inr i))
    simpa [dotProduct, Matrix.mulVec, sumArcs, Fintype.sum_sum_type] using add_nonneg hx hz

omit [DecidableEq A] [DecidableEq B] in
/-- Disjoint feasible SDP blocks remain feasible: cross cuts have RHS one half. -/
theorem sdp_sum {y X : Matrix A A ℝ} {z Z : Matrix B B ℝ}
    (hy : Feasible y X) (hz : Feasible z Z) :
    Feasible (sumArcs y z) (sumArcs X Z) := by
  constructor
  · rintro (i | i) (j | j) <;> simp [sumArcs, hy.nonneg, hz.nonneg]
  · rintro (i | i) <;> simp [sumArcs, hy.diagonal_y, hz.diagonal_y]
  · rintro (i | i)
    · simpa [sumArcs, Fintype.sum_sum_type] using hy.outdegree i
    · simpa [sumArcs, Fintype.sum_sum_type] using hz.outdegree i
  · exact psd_sum hy.psd hz.psd
  · rintro (i | i) <;> simp [sumArcs, hy.diagonal_X, hz.diagonal_X]
  · rintro (i | i) (j | j) hij
    · exact hy.cut_bound i j (fun h => hij (congrArg Sum.inl h))
    · norm_num [sumArcs, edgeWeights]
    · norm_num [sumArcs, edgeWeights]
    · exact hz.cut_bound i j (fun h => hij (congrArg Sum.inr h))

/-- Identity Gram matrix with zero arcs, including an empty background. -/
theorem sdp_zero : Feasible (0 : Matrix B B ℝ) 1 := by
  constructor
  · intros; simp
  · intros; simp
  · intros; simp
  · exact Matrix.PosSemidef.one
  · intros; simp
  · intro i j hij; simp [edgeWeights, hij]

theorem sdp_witness {z Z : Matrix B B ℝ} (hz : Feasible z Z) :
    Feasible (sumArcs cycleY z) (sumArcs cycleX Z) ∧
    objective (subsetCost (leftVertices (A := Fin 4) (B := B)))
      (projection (sumArcs cycleY z)) = 4 := by
  refine ⟨sdp_sum four_cycle_feasible hz, ?_⟩
  rw [objective_left _ _ four_cycle_feasible.diagonal_y hz.diagonal_y, four_cycle_weight]

/-- No smaller factor works on Fin 4 plus any finite set of extra vertices.
The unit objective uses all six K4 edges; the witness has only four nonzero entries. -/
theorem sdp_factor_ge_four_thirds {beta : ℝ}
    (h : MaxApproximation (treeIncidence (V := Fin 4 ⊕ B)) sdpRelaxation beta) :
    (4 / 3 : ℝ) ≤ beta := by
  let U := leftVertices (A := Fin 4) (B := B)
  obtain ⟨hf, hv⟩ := sdp_witness (sdp_zero (B := B))
  have hh := h.objective_le (subsetCost U) (subsetCost_nonneg U) 3
    (fun T => by
      have ht := tree_subset_objective T.property U leftVertices_nonempty
      norm_num [U] at ht
      exact ht)
    (projection (sumArcs cycleY (0 : Matrix B B ℝ))) ⟨_, _, hf, rfl⟩
  rw [hv] at hh
  linarith

/-- Total mass of a projection, with diagonal unordered pairs contributing zero. -/
theorem projection_mass (y : Matrix A A ℝ) (hd : ∀ i, y i i = 0) :
    (∑ e, projection y e) = internalWeight (edgeWeights y) Finset.univ := by
  simpa using projection_subset_sum hd Finset.univ

theorem mass_sumArcs (y : Matrix A A ℝ) (z : Matrix B B ℝ)
    (hd : ∀ i, y i i = 0) (hzd : ∀ i, z i i = 0) :
    (∑ e, projection (sumArcs y z) e) = (∑ e, projection y e) + ∑ e, projection z e := by
  rw [projection_mass _ (by rintro (i | i) <;> simp [sumArcs, hd, hzd]),
    projection_mass y hd, projection_mass z hzd]
  simp [internalWeight_edgeWeights, sumArcs, Fintype.sum_sum_type]

omit [DecidableEq A] in
/-- Every actual tree satisfies the cardinality equation, including a singleton tree. -/
theorem tree_mass {G : SimpleGraph A} (hG : G.IsTree) :
    (∑ e, graphIncidence G e) = (Fintype.card A : ℝ) - 1 := by
  classical
  have he := objective_graphIncidence (fun _ => 1) G
  simp only [objective, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at he
  rw [he]
  have hc : (G.edgeFinset.card : ℝ) + 1 = Fintype.card A := by
    exact_mod_cast hG.card_edgeFinset
  linarith

/-- Optional equation x(E)=|V|-1, intersected with the actual relaxation. -/
def cardinalitySlice (R : Set (Sym2 A → ℝ)) : Set (Sym2 A → ℝ) :=
  {x | x ∈ R ∧ (∑ e, x e) = (Fintype.card A : ℝ) - 1}

omit [DecidableEq A] in
/-- Adding the cardinality equation preserves both containment and the guarantee. -/
theorem approximation_cardinalitySlice {R : Set (Sym2 A → ℝ)} {beta : ℝ}
    (h : MaxApproximation (treeIncidence (V := A)) R beta) :
    MaxApproximation treeIncidence (cardinalitySlice R) beta := by
  refine ⟨h.factor_ge_one, ?_, ?_⟩
  · intro T; exact ⟨h.contains T, tree_mass T.property⟩
  · intro c hc x hx; exact h.bound c hc x hx.1

/-- Cardinality-constrained LP witness on a triangle and a genuine background tree.
Nonemptiness is needed precisely to make that tree exist. -/
theorem lp_cardinality_witness [Nonempty B] :
    ∃ x ∈ cardinalitySlice (lpRelaxation (V := Fin 3 ⊕ B)),
      objective (subsetCost (leftVertices (A := Fin 3) (B := B))) x = 3 := by
  obtain ⟨T, _, hT⟩ := (connected_top (V := B)).exists_isTree_le
  obtain ⟨z, hz, hp⟩ := tree_lp_containment hT
  obtain ⟨hf, hv⟩ := lp_witness hz
  refine ⟨projection (sumArcs triangleY z), ⟨⟨_, hf, rfl⟩, ?_⟩, hv⟩
  rw [mass_sumArcs _ _ triangle_lp_feasible.diagonal hz.diagonal,
    projection_eq_graphIncidence hp, tree_mass hT, projection_mass _ triangle_lp_feasible.diagonal]
  norm_num [internalWeight, edgeWeights, triangleY, Fin.sum_univ_succ, Fintype.card_sum]
  ring

theorem sdp_cardinality_witness [Nonempty B] :
    ∃ x ∈ cardinalitySlice (sdpRelaxation (V := Fin 4 ⊕ B)),
      objective (subsetCost (leftVertices (A := Fin 4) (B := B))) x = 4 := by
  obtain ⟨T, _, hT⟩ := (connected_top (V := B)).exists_isTree_le
  obtain ⟨z, Z, hz, hp⟩ := tree_sdp_containment hT
  obtain ⟨hf, hv⟩ := sdp_witness hz
  refine ⟨projection (sumArcs cycleY z), ⟨⟨_, _, hf, rfl⟩, ?_⟩, hv⟩
  rw [mass_sumArcs _ _ four_cycle_feasible.diagonal_y hz.diagonal_y,
    projection_eq_graphIncidence hp, tree_mass hT, projection_mass _ four_cycle_feasible.diagonal_y,
    four_cycle_weight]
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem lp_cardinality_factor_ge_three_halves [Nonempty B] {beta : ℝ}
    (h : MaxApproximation (treeIncidence (V := Fin 3 ⊕ B))
      (cardinalitySlice lpRelaxation) beta) : (3 / 2 : ℝ) ≤ beta := by
  obtain ⟨x, hx, hv⟩ := lp_cardinality_witness (B := B)
  let U := leftVertices (A := Fin 3) (B := B)
  have hh := h.objective_le (subsetCost U) (subsetCost_nonneg U) 2
    (fun T => by
      have ht := tree_subset_objective T.property U leftVertices_nonempty
      norm_num [U] at ht
      exact ht) x hx
  rw [hv] at hh
  linarith

theorem sdp_cardinality_factor_ge_four_thirds [Nonempty B] {beta : ℝ}
    (h : MaxApproximation (treeIncidence (V := Fin 4 ⊕ B))
      (cardinalitySlice sdpRelaxation) beta) : (4 / 3 : ℝ) ≤ beta := by
  obtain ⟨x, hx, hv⟩ := sdp_cardinality_witness (B := B)
  let U := leftVertices (A := Fin 4) (B := B)
  have hh := h.objective_le (subsetCost U) (subsetCost_nonneg U) 3
    (fun T => by
      have ht := tree_subset_objective T.property U leftVertices_nonempty
      norm_num [U] at ht
      exact ht) x hx
  rw [hv] at hh
  linarith

/-- The factor is exactly 3/2, not merely a feasible point with that arithmetic ratio. -/
theorem lp_exact_factor :
    MaxApproximation (treeIncidence (V := Fin 3 ⊕ B)) lpRelaxation (3 / 2 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin 3 ⊕ B)) lpRelaxation beta →
      (3 / 2 : ℝ) ≤ beta :=
  ⟨lp_three_halves, fun _ => lp_factor_ge_three_halves⟩

theorem sdp_exact_factor :
    MaxApproximation (treeIncidence (V := Fin 4 ⊕ B)) sdpRelaxation (4 / 3 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin 4 ⊕ B)) sdpRelaxation beta →
      (4 / 3 : ℝ) ≤ beta :=
  ⟨sdp_four_thirds, fun _ => sdp_factor_ge_four_thirds⟩

theorem lp_cardinality_exact_factor [Nonempty B] :
    MaxApproximation (treeIncidence (V := Fin 3 ⊕ B))
      (cardinalitySlice lpRelaxation) (3 / 2 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin 3 ⊕ B))
      (cardinalitySlice lpRelaxation) beta → (3 / 2 : ℝ) ≤ beta :=
  ⟨approximation_cardinalitySlice lp_three_halves, fun _ => lp_cardinality_factor_ge_three_halves⟩

theorem sdp_cardinality_exact_factor [Nonempty B] :
    MaxApproximation (treeIncidence (V := Fin 4 ⊕ B))
      (cardinalitySlice sdpRelaxation) (4 / 3 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin 4 ⊕ B))
      (cardinalitySlice sdpRelaxation) beta → (4 / 3 : ℝ) ≤ beta :=
  ⟨approximation_cardinalitySlice sdp_four_thirds, fun _ => sdp_cardinality_factor_ge_four_thirds⟩

/- FormulationTransport.lean proves full equivalence transport of these actual
formulations, tree incidences, objectives and cardinality slices. Its four
*_fin_* endpoints give the exact corresponding Fin n thresholds. -/
end
end Lemmata.SpanningTreeSymmetricEF.ApproximationSharpness
