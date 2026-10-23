module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticOrthogonal

@[expose] public section


/-! Paper-facing single-cone formulations. Their projections are actual convex
hulls of spanning-tree incidence vectors; no integrality, orientation, or
small-index theorem is supplied as an assumption. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticEndpoints
open scoped Classical
open FormulationStructure QuadraticCore QuadraticAffine QuadraticRaw
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev TreePolytope (V : Type) [Fintype V] :=
  convexHull ℝ (Set.range (ApproximationUpper.treeIncidence (V := V)))

/-- Matrix order is `Fintype.card J`. There is exactly one PSD cone and no
additional scalar nonnegativity cones. -/
structure ExactPSDFormulation (J : Type) [Fintype J] (P : Set (Sym2 V → ℝ)) where
  affineSlice : AffineSubspace ℝ (Matrix J J ℝ)
  project : Matrix J J ℝ →ₗ[ℝ] (Sym2 V → ℝ)
  exact_projection : project '' ((affineSlice : Set (Matrix J J ℝ)) ∩ {Y | Y.PosSemidef}) = P

def fromImage {J : Type} [Fintype J] [DecidableEq J] (R : RootFamily V)
    (a : Edge V → J → ℝ) (b : V → V → J → ℝ) {P : Set (Sym2 V → ℝ)}
    (h : image R a b = P) : ExactPSDFormulation J P where
  affineSlice := slice R a b
  project := projection a
  exact_projection := (image_as_affine_psd R a b).symm.trans h

/-- Coordinate-permutation-symmetric exact model of order 3*binomial(n,2). -/
def symmetricRaw [Nonempty V] : ExactPSDFormulation (Label (allRoots (V := V))) (TreePolytope V) :=
  fromImage allRoots (edgeCoeff allRoots) (parentCoeff allRoots) symmetric_exact

/-- Ordered-root exact model of order 2*binomial(n,2). -/
def asymmetricRaw [Nonempty V] [LinearOrder V] :
    ExactPSDFormulation (Label (orderedRoots (V := V))) (TreePolytope V) :=
  fromImage orderedRoots (edgeCoeff orderedRoots) (parentCoeff orderedRoots) asymmetric_exact

/-- Exact compressed symmetric model in orthonormal coordinates. -/
def symmetricCompressed [Nonempty V] :
    ExactPSDFormulation (QuadraticOrthogonal.Index V) (TreePolytope V) :=
  fromImage allRoots QuadraticOrthogonal.edgeCoeff QuadraticOrthogonal.parentCoeff
    QuadraticOrthogonal.exact_image

/-- Exact compressed asymmetric model, removing one smallest-root coordinate. -/
def asymmetricCompressed [Nonempty V] [LinearOrder V] [OrderBot V] [Nontrivial V] :
    ExactPSDFormulation
      (QuadraticCompression.Kept (orderedRoots (V := V)) QuadraticOrders.asymmetricDeletion)
      (TreePolytope V) :=
  fromImage orderedRoots
    (QuadraticCompression.edgeCoeff orderedRoots QuadraticOrders.asymmetricDeletion)
    (QuadraticCompression.parentCoeff orderedRoots QuadraticOrders.asymmetricDeletion)
    (QuadraticCompression.exact_image (V := V) orderedRoots
      (QuadraticOrders.asymmetricDeletion (V := V)))

theorem symmetric_raw_size : Fintype.card (Label (allRoots (V := V))) =
    3 * (Fintype.card V).choose 2 := symmetric_order

theorem asymmetric_raw_size [LinearOrder V] : Fintype.card (Label (orderedRoots (V := V))) =
    2 * (Fintype.card V).choose 2 := QuadraticOrders.asymmetric_order

theorem symmetric_compressed_size [Nontrivial V] : Fintype.card (QuadraticOrthogonal.Index V) =
    3 * (Fintype.card V).choose 2 - Fintype.card V := by
  rw [Fintype.card_fin,QuadraticOrthogonal.compressed_order]

theorem asymmetric_compressed_size [LinearOrder V] [OrderBot V] [Nontrivial V] :
    Fintype.card (QuadraticCompression.Kept (orderedRoots (V := V)) QuadraticOrders.asymmetricDeletion) =
      2 * (Fintype.card V).choose 2 - 1 := by
  simpa only [Fintype.card_eq_nat_card] using QuadraticOrders.asymmetric_compressed_order (V := V)

/-- The displayed compressed symmetric formulation preserves its affine slice. -/
theorem symmetric_compressed_slice [Nonempty V] (g : Equiv.Perm V)
    {Y : Matrix (QuadraticOrthogonal.Index V) (QuadraticOrthogonal.Index V) ℝ}
    (h : Y ∈ (symmetricCompressed (V := V)).affineSlice) :
    QuadraticOrthogonal.affineAction g Y ∈ (symmetricCompressed (V := V)).affineSlice :=
  QuadraticOrthogonal.slice_preserved g h

/-- Projection commutes with the coherent orthogonal-congruence action. -/
theorem symmetric_compressed_equivariant [Nonempty V] (g : Equiv.Perm V)
    (Y : Matrix (QuadraticOrthogonal.Index V) (QuadraticOrthogonal.Index V) ℝ) :
    (symmetricCompressed (V := V)).project (QuadraticOrthogonal.affineAction g Y) =
      permuteVector g ((symmetricCompressed (V := V)).project Y) :=
  QuadraticOrthogonal.projection_covariant g Y

/-- A single quadratic-order cone suffices on any finite ordered vertex set
with a smallest vertex and at least two vertices. -/
theorem asymmetric_quadratic_lift [Nonempty V] [LinearOrder V] [OrderBot V] [Nontrivial V] :
    Nonempty (ExactPSDFormulation
      (QuadraticCompression.Kept (orderedRoots (V := V)) QuadraticOrders.asymmetricDeletion)
      (TreePolytope V)) ∧
    Fintype.card (QuadraticCompression.Kept (orderedRoots (V := V)) QuadraticOrders.asymmetricDeletion) =
      2 * (Fintype.card V).choose 2 - 1 :=
  ⟨⟨asymmetricCompressed⟩,asymmetric_compressed_size⟩

/-- Exactness and the matrix order of the orthogonally symmetric compression. -/
theorem symmetric_quadratic_lift [Nonempty V] [Nontrivial V] :
    Nonempty (ExactPSDFormulation (QuadraticOrthogonal.Index V) (TreePolytope V)) ∧
    Fintype.card (QuadraticOrthogonal.Index V) = 3 * (Fintype.card V).choose 2 - Fintype.card V :=
  ⟨⟨symmetricCompressed⟩,symmetric_compressed_size⟩

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticEndpoints
