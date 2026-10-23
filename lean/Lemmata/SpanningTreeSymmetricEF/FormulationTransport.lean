module

public import Lemmata.SpanningTreeSymmetricEF.ApproximationSharpness
public import Lemmata.SpanningTreeSymmetricEF.FormulationStructure

@[expose] public section


/-! Equivalence transport of the actual formulations, including finite-label sharpness. -/
namespace Lemmata.SpanningTreeSymmetricEF.FormulationTransport
open scoped BigOperators
open SimpleGraph SDPBounds TreeModels ApproximationUpper Approximation ApproximationSharpness
noncomputable section

variable {V W : Type*}

/-- The equivalence on unordered pairs includes diagonal pairs. -/
def sym2Equiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv q := by induction q using Sym2.inductionOn with | _ i j => simp
  right_inv q := by induction q using Sym2.inductionOn with | _ i j => simp

def reindexMatrix (e : V ≃ W) (M : Matrix V V ℝ) : Matrix W W ℝ :=
  M.submatrix e.symm e.symm

def reindexVector (e : V ≃ W) (x : Sym2 V → ℝ) : Sym2 W → ℝ :=
  fun q => x ((sym2Equiv e).symm q)

@[simp] theorem reindexMatrix_inverse (e : V ≃ W) (M : Matrix V V ℝ) :
    reindexMatrix e.symm (reindexMatrix e M) = M := by
  ext i j; simp [reindexMatrix]

@[simp] theorem reindexVector_inverse (e : V ≃ W) (x : Sym2 V → ℝ) :
    reindexVector e.symm (reindexVector e x) = x := by
  funext q
  exact congrArg x ((sym2Equiv e).left_inv q)

@[simp] theorem reindexVector_inverse' (e : V ≃ W) (x : Sym2 W → ℝ) :
    reindexVector e (reindexVector e.symm x) = x :=
  reindexVector_inverse e.symm x

theorem projection_reindex (e : V ≃ W) (y : Matrix V V ℝ) :
    projection (reindexMatrix e y) = reindexVector e (projection y) := by
  funext q
  induction q using Sym2.inductionOn with | _ i j => rfl

variable [Fintype V] [Fintype W]

theorem lp_reindex (e : V ≃ W) {y : Matrix V V ℝ} (h : LPFeasible y) :
    LPFeasible (reindexMatrix e y) := by
  refine ⟨fun i j => h.nonneg _ _, fun i => h.diagonal _, ?_, fun i j => h.capacity _ _⟩
  intro i
  change (∑ j, y (e.symm i) (e.symm j)) ≤ 1
  rw [e.symm.sum_comp]
  exact h.outdegree _

theorem sdp_reindex (e : V ≃ W) {y X : Matrix V V ℝ} (h : Feasible y X) :
    Feasible (reindexMatrix e y) (reindexMatrix e X) := by
  refine ⟨fun i j => h.nonneg _ _, fun i => h.diagonal_y _, ?_,
    h.psd.submatrix e.symm, fun i => h.diagonal_X _, ?_⟩
  · intro i
    change (∑ j, y (e.symm i) (e.symm j)) ≤ 1
    rw [e.symm.sum_comp]
    exact h.outdegree _
  · intro i j hij
    exact h.cut_bound _ _ (e.symm.injective.ne hij)

theorem lp_reindex_iff (e : V ≃ W) (y : Matrix V V ℝ) :
    LPFeasible (reindexMatrix e y) ↔ LPFeasible y :=
  ⟨fun h => by simpa using lp_reindex e.symm h, lp_reindex e⟩

theorem sdp_reindex_iff (e : V ≃ W) (y X : Matrix V V ℝ) :
    Feasible (reindexMatrix e y) (reindexMatrix e X) ↔ Feasible y X :=
  ⟨fun h => by simpa using sdp_reindex e.symm h, sdp_reindex e⟩

theorem lpRelaxation_reindex (e : V ≃ W) {x : Sym2 V → ℝ} (h : x ∈ lpRelaxation) :
    reindexVector e x ∈ lpRelaxation := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨_, lp_reindex e hy, projection_reindex e y⟩

theorem sdpRelaxation_reindex (e : V ≃ W) {x : Sym2 V → ℝ} (h : x ∈ sdpRelaxation) :
    reindexVector e x ∈ sdpRelaxation := by
  obtain ⟨y, X, hy, rfl⟩ := h
  exact ⟨_, _, sdp_reindex e hy, projection_reindex e y⟩

theorem lpRelaxation_reindex_iff (e : V ≃ W) (x : Sym2 V → ℝ) :
    reindexVector e x ∈ lpRelaxation ↔ x ∈ lpRelaxation :=
  ⟨fun h => by simpa using lpRelaxation_reindex e.symm h, lpRelaxation_reindex e⟩

theorem sdpRelaxation_reindex_iff (e : V ≃ W) (x : Sym2 V → ℝ) :
    reindexVector e x ∈ sdpRelaxation ↔ x ∈ sdpRelaxation :=
  ⟨fun h => by simpa using sdpRelaxation_reindex e.symm h, sdpRelaxation_reindex e⟩

theorem objective_reindex (e : V ≃ W) (c x : Sym2 V → ℝ) :
    objective (reindexVector e c) (reindexVector e x) = objective c x :=
  (sym2Equiv e).symm.sum_comp (fun q => c q * x q)

theorem mass_reindex (e : V ≃ W) (x : Sym2 V → ℝ) :
    (∑ q, reindexVector e x q) = ∑ q, x q := (sym2Equiv e).symm.sum_comp x

theorem cardinalitySlice_reindex_iff (e : V ≃ W)
    {R : Set (Sym2 V → ℝ)} {S : Set (Sym2 W → ℝ)}
    (h : ∀ x, reindexVector e x ∈ S ↔ x ∈ R) (x : Sym2 V → ℝ) :
    reindexVector e x ∈ cardinalitySlice S ↔ x ∈ cardinalitySlice R := by
  simp only [cardinalitySlice, Set.mem_ofPred_eq, h, mass_reindex, Fintype.card_congr e]

/-- Actual graph trees, not an abstract incidence-vector surrogate. -/
def reindexTree (e : V ≃ W) (T : SpanningTree V) : SpanningTree W :=
  ⟨T.val.map e.toEmbedding, (SimpleGraph.Iso.map e T.val).isTree_iff.mp T.property⟩

omit [Fintype V] [Fintype W] in
@[simp] theorem reindexTree_inverse (e : V ≃ W) (T : SpanningTree V) :
    reindexTree e.symm (reindexTree e T) = T := by
  apply Subtype.ext
  exact (SimpleGraph.map_symm _ e).trans (SimpleGraph.comap_map_eq e.toEmbedding T.val)

/-- A vertex equivalence gives a genuine equivalence of the types of actual trees. -/
def treeEquiv (e : V ≃ W) : SpanningTree V ≃ SpanningTree W where
  toFun := reindexTree e
  invFun := reindexTree e.symm
  left_inv := reindexTree_inverse e
  right_inv := reindexTree_inverse e.symm

omit [Fintype W] in
theorem treeIncidence_reindex (e : V ≃ W) (T : SpanningTree V) :
    treeIncidence (reindexTree e T) = reindexVector e (treeIncidence T) := by
  classical
  funext q
  induction q using Sym2.inductionOn with
  | _ i j =>
    simp only [treeIncidence, reindexTree, graphIncidence, reindexVector,
      sym2Equiv, Equiv.coe_fn_symm_mk, Sym2.map_mk, mem_edgeSet]
    have hh := (SimpleGraph.Iso.map e T.val).map_adj_iff
      (v := e.symm i) (w := e.symm j)
    change (T.val.map e.toEmbedding).Adj (e (e.symm i)) (e (e.symm j)) ↔
      T.val.Adj (e.symm i) (e.symm j) at hh
    simpa using congrArg (fun p : Prop => if p then (1 : ℝ) else 0) (propext hh)

/-- Transport the entire approximation property through a genuine vertex equivalence. -/
theorem maxApproximation_reindex (e : V ≃ W)
    {R : Set (Sym2 V → ℝ)} {S : Set (Sym2 W → ℝ)} {beta : ℝ}
    (hRS : ∀ x, reindexVector e x ∈ S ↔ x ∈ R)
    (h : MaxApproximation treeIncidence R beta) :
    MaxApproximation treeIncidence S beta := by
  refine ⟨h.factor_ge_one, ?_, ?_⟩
  · intro T
    have hh := (hRS _).mpr (h.contains (reindexTree e.symm T))
    simpa [treeIncidence_reindex] using hh
  · intro c hc x hx
    have hx' : reindexVector e.symm x ∈ R := by
      apply (hRS _).mp
      simpa using hx
    obtain ⟨T, hT⟩ := h.bound (reindexVector e.symm c) (fun q => hc _) _ hx'
    refine ⟨reindexTree e T, ?_⟩
    rw [objective_reindex] at hT
    have heq := objective_reindex e (reindexVector e.symm c) (treeIncidence T)
    simpa only [reindexVector_inverse', treeIncidence_reindex] using hT.trans_eq
      (congrArg (fun z => beta * z) heq.symm)

/-- Both directions are proved; no transport assumption remains for concrete models below. -/
theorem maxApproximation_reindex_iff (e : V ≃ W)
    {R : Set (Sym2 V → ℝ)} {S : Set (Sym2 W → ℝ)} {beta : ℝ}
    (hRS : ∀ x, reindexVector e x ∈ S ↔ x ∈ R) :
    MaxApproximation treeIncidence S beta ↔ MaxApproximation treeIncidence R beta := by
  constructor
  · apply maxApproximation_reindex e.symm
    intro x
    simpa using (hRS (reindexVector e.symm x)).symm
  · exact maxApproximation_reindex e hRS

theorem lp_approximation_reindex_iff (e : V ≃ W) (beta : ℝ) :
    MaxApproximation (treeIncidence (V := W)) lpRelaxation beta ↔
      MaxApproximation (treeIncidence (V := V)) lpRelaxation beta :=
  maxApproximation_reindex_iff e (lpRelaxation_reindex_iff e)

theorem sdp_approximation_reindex_iff (e : V ≃ W) (beta : ℝ) :
    MaxApproximation (treeIncidence (V := W)) sdpRelaxation beta ↔
      MaxApproximation (treeIncidence (V := V)) sdpRelaxation beta :=
  maxApproximation_reindex_iff e (sdpRelaxation_reindex_iff e)

theorem lp_cardinality_approximation_reindex_iff (e : V ≃ W) (beta : ℝ) :
    MaxApproximation (treeIncidence (V := W)) (cardinalitySlice lpRelaxation) beta ↔
      MaxApproximation (treeIncidence (V := V)) (cardinalitySlice lpRelaxation) beta :=
  maxApproximation_reindex_iff e (cardinalitySlice_reindex_iff e (lpRelaxation_reindex_iff e))

theorem sdp_cardinality_approximation_reindex_iff (e : V ≃ W) (beta : ℝ) :
    MaxApproximation (treeIncidence (V := W)) (cardinalitySlice sdpRelaxation) beta ↔
      MaxApproximation (treeIncidence (V := V)) (cardinalitySlice sdpRelaxation) beta :=
  maxApproximation_reindex_iff e (cardinalitySlice_reindex_iff e (sdpRelaxation_reindex_iff e))

/-- Canonical labels for a distinguished block and its (possibly empty) background. -/
def finBlockEquiv (k n : ℕ) (h : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_sub_of_le h)))

/-- Exact LP factor on the actual n-label model; n=3 has empty background. -/
theorem lp_fin_exact_factor (n : ℕ) (hn : 3 ≤ n) :
    MaxApproximation (treeIncidence (V := Fin n)) lpRelaxation (3 / 2 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin n)) lpRelaxation beta →
      (3 / 2 : ℝ) ≤ beta := by
  let e := finBlockEquiv 3 n hn
  exact ⟨(lp_approximation_reindex_iff e _).mpr lp_exact_factor.1,
    fun beta h => lp_exact_factor.2 beta ((lp_approximation_reindex_iff e beta).mp h)⟩

/-- Exact SDP factor on the actual n-label model; n=4 has empty background. -/
theorem sdp_fin_exact_factor (n : ℕ) (hn : 4 ≤ n) :
    MaxApproximation (treeIncidence (V := Fin n)) sdpRelaxation (4 / 3 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin n)) sdpRelaxation beta →
      (4 / 3 : ℝ) ≤ beta := by
  let e := finBlockEquiv 4 n hn
  exact ⟨(sdp_approximation_reindex_iff e _).mpr sdp_exact_factor.1,
    fun beta h => sdp_exact_factor.2 beta ((sdp_approximation_reindex_iff e beta).mp h)⟩

/-- The cardinality slice needs one background vertex, so its threshold is four. -/
theorem lp_fin_cardinality_exact_factor (n : ℕ) (hn : 4 ≤ n) :
    MaxApproximation (treeIncidence (V := Fin n)) (cardinalitySlice lpRelaxation) (3 / 2 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin n)) (cardinalitySlice lpRelaxation) beta →
      (3 / 2 : ℝ) ≤ beta := by
  let : NeZero (n - 3) := ⟨by omega⟩
  let e := finBlockEquiv 3 n (by omega)
  exact ⟨(lp_cardinality_approximation_reindex_iff e _).mpr lp_cardinality_exact_factor.1,
    fun beta h => lp_cardinality_exact_factor.2 beta
      ((lp_cardinality_approximation_reindex_iff e beta).mp h)⟩

/-- The cardinality slice needs one background vertex, so its threshold is five. -/
theorem sdp_fin_cardinality_exact_factor (n : ℕ) (hn : 5 ≤ n) :
    MaxApproximation (treeIncidence (V := Fin n)) (cardinalitySlice sdpRelaxation) (4 / 3 : ℝ) ∧
    ∀ beta, MaxApproximation (treeIncidence (V := Fin n)) (cardinalitySlice sdpRelaxation) beta →
      (4 / 3 : ℝ) ≤ beta := by
  let : NeZero (n - 4) := ⟨by omega⟩
  let e := finBlockEquiv 4 n (by omega)
  exact ⟨(sdp_cardinality_approximation_reindex_iff e _).mpr sdp_cardinality_exact_factor.1,
    fun beta h => sdp_cardinality_exact_factor.2 beta
      ((sdp_cardinality_approximation_reindex_iff e beta).mp h)⟩

end
end Lemmata.SpanningTreeSymmetricEF.FormulationTransport
