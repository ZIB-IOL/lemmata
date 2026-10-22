module

public import Lemmata.SpanningTreeSymmetricEF.LPResults
public import Lemmata.SpanningTreeSymmetricEF.UpperLP
public import Lemmata.SpanningTreeSymmetricEF.EdgeCoordinates
public import Lemmata.SpanningTreeSymmetricEF.PSDModels
public import Lemmata.SpanningTreeSymmetricEF.NonnegativeOuter

@[expose] public section

namespace Lemmata.SpanningTreeSymmetricEF

open scoped BigOperators Classical
noncomputable section

-- DOCS_BEGIN_MAIN
section LinearLowerBounds
variable {n : ℕ} {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

/-- Conditional Hamilton-path threshold for every finite affine-symmetric LP. -/
theorem hamilton_threshold (smallIndex : SmallIndexK3Criterion) (hn : 13 ≤ n)
    (L : SymmetricLP n E J) (hrows : Fintype.card J < n.choose 3)
    (β : ℝ) (happrox : L.Approximates β) :
    (3 / 2 : ℝ) * (1 - 1 / (n : ℝ)) ≤ β :=
  PolyhedralNormalForm.affine_lp_factor_lower L.slice L.slack L.project L.action
    L.stable L.covariant smallIndex hn hrows β
    ((L.approximates_iff_source β).mp happrox)

/-- Exactness supplies factor one; this proof uses no separate K6 certificate. -/
theorem exact_lp_lower (smallIndex : SmallIndexK3Criterion) (hn : 13 ≤ n)
    (L : SymmetricLP n E J) (hexact : L.Exact) : n.choose 3 ≤ Fintype.card J := by
  apply LPResults.exact_size_lower L.slice L.slack L.project L.action
    L.stable L.covariant smallIndex hn
  exact hexact.trans (treePolytope_eq_source n)

/-- Finite sufficiently-large-n form for every fixed factor below 3/2. -/
theorem fixed_factor_lp_lower (smallIndex : SmallIndexK3Criterion) (hn : 13 ≤ n)
    (L : SymmetricLP n E J) (β : ℝ) (hβ : β < 3 / 2)
    (hlarge : 3 / (3 - 2 * β) < (n : ℝ)) (happrox : L.Approximates β) :
    n.choose 3 ≤ Fintype.card J :=
  PolyhedralNormalForm.affine_lp_size_lower_of_fixed_factor
    L.slice L.slack L.project L.action L.stable L.covariant smallIndex hn β hβ hlarge
    ((L.approximates_iff_source β).mp happrox)
end LinearLowerBounds

/-- Literal row count, symmetry and sharp approximation factor of one concrete LP. -/
theorem symmetric_lp_upper (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (FormulationStructure.ScalarConstraint (Fin n)) =
      3 * n.choose 2 + n ∧
    (orientationLP n).Approximates (3 / 2 : ℝ) ∧
    ∀ β, (orientationLP n).Approximates β → (3 / 2 : ℝ) ≤ β :=
  ⟨orientationLP_count n, orientationLP_factor n hn⟩

/-- Intersecting the concrete image with the tree-cardinality hyperplane does
not improve its worst-case approximation factor once n ≥ 4. -/
theorem cardinality_slice_factor (n : ℕ) (hn : 4 ≤ n) :
    Approximation.MaxApproximation (SpanningTreeMinSplit.edgeValue (n := n))
      (ApproximationSharpness.cardinalitySlice (orientationLP n).image) (3 / 2 : ℝ) ∧
    ∀ β, Approximation.MaxApproximation (SpanningTreeMinSplit.edgeValue (n := n))
      (ApproximationSharpness.cardinalitySlice (orientationLP n).image) β →
      (3 / 2 : ℝ) ≤ β := by
  have h : SpanningTreeMinSplit.edgeValue (n := n) =
      ApproximationUpper.treeIncidence (V := Fin n) := funext incidence_eq_source
  simpa only [h, orientationLP_image] using
    FormulationTransport.lp_fin_cardinality_exact_factor n hn

/-- One cone of order 3m, with a coherent coordinate-permutation action. -/
theorem symmetric_raw_sdp (n : ℕ) (hn : 2 ≤ n) :
    HasPermutationPSD n (3 * n.choose 2) := by
  let : NeZero n := ⟨by omega⟩
  unfold HasPermutationPSD
  rw [treePolytope_eq_source]
  let F := SDPResults.symmetricRawModel (V := Fin n)
  exact ⟨_, inferInstance, inferInstance, F.formulation,
    by simpa using F.order_eq, ⟨F.symmetry⟩⟩

/-- One cone of order 3m-n, with a coherent orthogonal-congruence action. -/
theorem symmetric_compressed_sdp (n : ℕ) (hn : 2 ≤ n) :
    HasOrthogonalPSD n (3 * n.choose 2 - n) := by
  let : NeZero n := ⟨by omega⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  unfold HasOrthogonalPSD
  rw [treePolytope_eq_source]
  let F := SDPResults.symmetricCompressedModel (V := Fin n)
  exact ⟨_, inferInstance, inferInstance, F.formulation,
    by simpa using F.order_eq, ⟨F.symmetry⟩⟩

/-- The ordered-root constructions: existence, with no symmetry requirement. -/
theorem ordered_sdps (n : ℕ) (hn : 2 ≤ n) :
    HasExactPSD n (2 * n.choose 2) ∧ HasExactPSD n (2 * n.choose 2 - 1) := by
  let : NeZero n := ⟨by omega⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  constructor
  · unfold HasExactPSD
    rw [treePolytope_eq_source]
    have h := SDPResults.ordered_raw (V := Fin n)
    exact ⟨_, inferInstance, by simpa using h.2, h.1⟩
  · unfold HasExactPSD
    rw [treePolytope_eq_source]
    have h := SDPResults.ordered_compressed (V := Fin n)
    exact ⟨_, inferInstance, by simpa using h.2, h.1⟩

/-- Direct product-PSD lower bound: nonnegative image is essential; symmetry is not. -/
theorem nonnegative_outer_psd_lower {n : ℕ} (hn : 2 ≤ n)
    {E B : Type*} {K : B → Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype B] [∀ b, Fintype (K b)] (L : PSDPresentation n E B K)
    (hcontains : treePolytope n ⊆ L.image)
    (hnonneg : ∀ x ∈ L.image, ∀ e, 0 ≤ x e) :
    (n - 1).choose 2 ≤ ∑ b, Fintype.card (K b) := by
  let : NeZero n := ⟨by omega⟩
  have h := NonnegativeOuter.sdp_size_lower_of_polytope_containment
    L.slice L.block L.project (by rwa [← treePolytope_eq_source]) hnonneg
  simpa using h
-- DOCS_END_MAIN

end
end Lemmata.SpanningTreeSymmetricEF
