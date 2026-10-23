module

/-
  End-to-end nonnegative-objective guarantees for the actual orientation LP
  and cut-matrix SDP, including containment of every spanning-tree vertex.

  Coordinates are unordered pairs with diagonal coordinates fixed to zero;
  the diagonal entries contribute nothing to any objective. Forest domination
  is proved by weight induction, not assumed as an Edmonds/matching interface.
-/
public import Lemmata.SpanningTreeSymmetricEF.TreeModels
public import Lemmata.SpanningTreeSymmetricEF.ForestPolytope
public import Lemmata.SpanningTreeSymmetricEF.Approximation

@[expose] public section


namespace Lemmata.SpanningTreeSymmetricEF.ApproximationUpper

open scoped BigOperators
open SimpleGraph SDPBounds TreeModels Approximation

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual unordered-edge projection of orientation variables. -/
def projection (y : Matrix V V ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨edgeWeights y, fun _ _ => add_comm _ _⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem projection_mk (y : Matrix V V ℝ) (i j : V) :
    projection y s(i,j) = edgeWeights y i j := rfl

/-- Coordinates of an actual simple graph, extended by zero on the diagonal. -/
def graphIncidence (G : SimpleGraph V) (e : Sym2 V) : ℝ := by
  classical
  exact if e ∈ G.edgeSet then 1 else 0

abbrev SpanningTree (V : Type*) := {G : SimpleGraph V // G.IsTree}

def treeIncidence (T : SpanningTree V) : Sym2 V → ℝ := graphIncidence T.val

def lpRelaxation : Set (Sym2 V → ℝ) :=
  {x | ∃ y : Matrix V V ℝ, LPFeasible y ∧ projection y = x}

def sdpRelaxation : Set (Sym2 V → ℝ) :=
  {x | ∃ y X : Matrix V V ℝ, Feasible y X ∧ projection y = x}

omit [Fintype V] in
/-- Unordered-pair sum equals half the ordered-pair sum when the diagonal is zero. -/
theorem sum_sym2_eq_half_sum (f : Sym2 V → ℝ) (hdiag : ∀ i, f s(i,i) = 0)
    (U : Finset V) : (∑ e ∈ U.sym2, f e) = (∑ i ∈ U, ∑ j ∈ U, f s(i,j)) / 2 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    have hdisj : Disjoint ((insert a U).image (fun b => s(a,b))) U.sym2 := by
      rw [Finset.disjoint_left]
      intro e he hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
      exact ha (Finset.mk_mem_sym2_iff.mp hu).1
    have hinj : ∀ b ∈ insert a U, ∀ c ∈ insert a U, s(a,b) = s(a,c) → b = c := by
      intro b _ c _ hh
      rcases Sym2.eq_iff.mp hh with h | h <;> aesop
    have hswap : (∑ i ∈ U, f s(i,a)) = ∑ i ∈ U, f s(a,i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Sym2.eq_swap]
    rw [Finset.sym2_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
    simp only [Finset.sum_insert ha, hdiag, zero_add]
    simp_rw [Finset.sum_add_distrib]
    rw [hswap]
    linarith

omit [Fintype V] [DecidableEq V] in
theorem projection_nonnegative {y : Matrix V V ℝ} (hy : ∀ i j, 0 ≤ y i j)
    (e : Sym2 V) : 0 ≤ projection y e := by
  induction e using Sym2.inductionOn with
  | _ i j => exact add_nonneg (hy i j) (hy j i)

omit [Fintype V] [DecidableEq V] in
theorem projection_diagonal {y : Matrix V V ℝ} (hy : ∀ i, y i i = 0)
    (e : Sym2 V) (he : e.IsDiag) : projection y e = 0 := by
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hij := Sym2.mk_isDiag_iff.mp he
    subst j
    simp [projection, edgeWeights, hy]

omit [Fintype V] in
theorem projection_subset_sum {y : Matrix V V ℝ} (hy : ∀ i, y i i = 0)
    (U : Finset V) : (∑ e ∈ U.sym2, projection y e) = internalWeight (edgeWeights y) U := by
  exact sum_sym2_eq_half_sum (projection y) (by intro i; simp [edgeWeights, hy]) U

omit [Fintype V] [DecidableEq V] in
theorem projection_eq_graphIncidence {G : SimpleGraph V} {y : Matrix V V ℝ}
    (h : edgeWeights y = TreeModels.incidence G) : projection y = graphIncidence G := by
  classical
  funext e
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hh := congrFun (congrFun h i) j
    simpa [graphIncidence, TreeModels.incidence] using hh

omit [DecidableEq V] in
theorem objective_graphIncidence (c : Sym2 V → ℝ) (G : SimpleGraph V) :
    letI := Classical.decRel G.Adj
    objective c (graphIncidence G) = ∑ e ∈ G.edgeFinset, c e := by
  classical
  unfold objective graphIncidence
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext e; simp
  · intro e _; rfl

theorem sum_top_edges_eq_sum [Fintype (⊤ : SimpleGraph V).edgeSet] (f : Sym2 V → ℝ) (hdiag : ∀ e, e.IsDiag → f e = 0) :
    (∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, f e) = ∑ e, f e := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  apply hdiag
  simpa [mem_edgeFinset, edgeSet_top, Sym2.mem_diagSet] using he

/-- Genuine objective domination obtained from the scaled subset inequalities.
The only inputs are actual orientation variables and their scalar constraints. -/
theorem scaled_objective_dominance [Nonempty V] (y : Matrix V V ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hdiag : ∀ i, y i i = 0)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hsub : ∀ U : Finset V, U.Nonempty →
      scale * internalWeight (edgeWeights y) U ≤ (U.card : ℝ) - 1)
    (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ T : SimpleGraph V, T.IsTree ∧
      scale * objective c (projection y) ≤ objective c (graphIncidence T) := by
  classical
  let x : Sym2 V → ℝ := fun e => scale * projection y e
  have hx : ∀ e, 0 ≤ x e := fun e => mul_nonneg hscale (projection_nonnegative hy e)
  have hxd : ∀ e, e.IsDiag → x e = 0 := by
    intro e he
    simp [x, projection_diagonal hdiag e he]
  have hxu : ∀ U : Finset V, U.Nonempty → (∑ e ∈ U.sym2, x e) ≤ (U.card : ℝ) - 1 := by
    intro U hU
    simpa only [x, ← Finset.mul_sum, projection_subset_sum hdiag U] using hsub U hU
  obtain ⟨T, hT, _, hw⟩ := ForestPolytope.weighted_spanning_tree_dominance x hx hxd hxu
    (⊤ : SimpleGraph V) connected_top c hc
  refine ⟨T, hT, ?_⟩
  rw [← objective_graphIncidence c T] at hw
  have hw' : (∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, c e * x e) ≤
      objective c (graphIncidence T) := by
    convert hw using 1
    apply Finset.sum_congr
    · ext e; simp
    · intro e _; rfl
  rw [sum_top_edges_eq_sum (fun e => c e * x e) (by intro e he; simp [hxd e he])] at hw'
  have heq : (∑ e, c e * x e) = scale * objective c (projection y) := by
    simp only [x, objective, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rwa [heq] at hw'

/-- Full nonnegative-maximization guarantee, including tree containment,
for the actual orientation LP. No integrality theorem is assumed. -/
theorem lp_three_halves [Nonempty V] :
    MaxApproximation (treeIncidence (V := V)) lpRelaxation (3 / 2 : ℝ) := by
  classical
  refine ⟨by norm_num, ?_, ?_⟩
  · intro T
    obtain ⟨y, hy, hp⟩ := tree_lp_containment T.property
    exact ⟨y, hy, projection_eq_graphIncidence hp⟩
  · intro c hc x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨T, hT, hw⟩ := scaled_objective_dominance y hy.nonneg hy.diagonal
      (2 / 3 : ℝ) (by norm_num) hy.scaled_forest_inequality c hc
    refine ⟨⟨T, hT⟩, ?_⟩
    change objective c (projection y) ≤ (3 / 2 : ℝ) * objective c (graphIncidence T)
    linarith

/-- Full nonnegative-maximization guarantee, including an actual feasible
rank-one lift for every tree, for the cut-matrix SDP. -/
theorem sdp_four_thirds [Nonempty V] :
    MaxApproximation (treeIncidence (V := V)) sdpRelaxation (4 / 3 : ℝ) := by
  classical
  refine ⟨by norm_num, ?_, ?_⟩
  · intro T
    obtain ⟨y, X, hy, hp⟩ := tree_sdp_containment T.property
    exact ⟨y, X, hy, projection_eq_graphIncidence hp⟩
  · intro c hc x hx
    obtain ⟨y, X, hy, rfl⟩ := hx
    obtain ⟨T, hT, hw⟩ := scaled_objective_dominance y hy.nonneg hy.diagonal_y
      (3 / 4 : ℝ) (by norm_num) hy.scaled_forest_inequality c hc
    refine ⟨⟨T, hT⟩, ?_⟩
    change objective c (projection y) ≤ (4 / 3 : ℝ) * objective c (graphIncidence T)
    linarith

end
end Lemmata.SpanningTreeSymmetricEF.ApproximationUpper
