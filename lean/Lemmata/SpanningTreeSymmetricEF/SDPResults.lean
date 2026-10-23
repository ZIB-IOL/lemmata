module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticEndpoints

@[expose] public section

/-! Exact single-cone formulations with symmetry attached to the very same
slice and projection. Ordered models assert existence, not absence of symmetry. -/
namespace Lemmata.SpanningTreeSymmetricEF.SDPResults
open scoped Classical
open Matrix FormulationStructure QuadraticEndpoints
noncomputable section
variable {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- A coherent coordinate-permutation action on an exact formulation.
The transformation is explicitly simultaneous row/column reindexing. -/
structure PermutationSymmetry {P : Set (Sym2 V → ℝ)} (F : ExactPSDFormulation J P) where
  action : Equiv.Perm V →* Equiv.Perm J
  slice_preserved : ∀ g Y, Y ∈ F.affineSlice →
    Y.submatrix (action g).symm (action g).symm ∈ F.affineSlice
  feasible_preserved : ∀ g Y, Y ∈ F.affineSlice ∧ Y.PosSemidef →
    Y.submatrix (action g).symm (action g).symm ∈ F.affineSlice ∧
      (Y.submatrix (action g).symm (action g).symm).PosSemidef
  projection_covariant : ∀ g Y,
    F.project (Y.submatrix (action g).symm (action g).symm) =
      permuteVector g (F.project Y)

/-- A coherent orthogonal action on the specified exact formulation.
The transformation is explicitly `U * Y * Uᵀ`, not an unrelated affine action. -/
structure OrthogonalSymmetry {P : Set (Sym2 V → ℝ)} (F : ExactPSDFormulation J P) where
  action : Equiv.Perm V →* Matrix.orthogonalGroup J ℝ
  slice_preserved : ∀ g Y, Y ∈ F.affineSlice →
    (action g : Matrix J J ℝ) * Y * (action g : Matrix J J ℝ)ᵀ ∈ F.affineSlice
  feasible_preserved : ∀ g Y, Y ∈ F.affineSlice ∧ Y.PosSemidef →
    (action g : Matrix J J ℝ) * Y * (action g : Matrix J J ℝ)ᵀ ∈ F.affineSlice ∧
      ((action g : Matrix J J ℝ) * Y * (action g : Matrix J J ℝ)ᵀ).PosSemidef
  projection_covariant : ∀ g Y,
    F.project ((action g : Matrix J J ℝ) * Y * (action g : Matrix J J ℝ)ᵀ) =
      permuteVector g (F.project Y)

/-- Exactness, order and coordinate-permutation symmetry of one formulation. -/
structure PermutationSymmetricModel (V J : Type) [Fintype V] [Fintype J]
    [DecidableEq J] (k : ℕ) where
  formulation : ExactPSDFormulation J (TreePolytope V)
  order_eq : Fintype.card J = k
  symmetry : PermutationSymmetry formulation

/-- Exactness, order and orthogonal-congruence symmetry of one formulation. -/
structure OrthogonalSymmetricModel (V J : Type) [Fintype V] [Fintype J]
    [DecidableEq J] (k : ℕ) where
  formulation : ExactPSDFormulation J (TreePolytope V)
  order_eq : Fintype.card J = k
  symmetry : OrthogonalSymmetry formulation

/-- The raw all-root model, with its actual coordinate-permutation action. -/
def symmetricRawModel [Nonempty V] :
    PermutationSymmetricModel V (QuadraticSymmetry.Labels V)
      (3 * (Fintype.card V).choose 2) where
  formulation := symmetricRaw
  order_eq := symmetric_raw_size
  symmetry := {
    action := QuadraticSymmetry.labelAction
    slice_preserved := fun g _ h => QuadraticSymmetry.slice_preserved g h
    feasible_preserved := fun g _ h =>
      let h' := QuadraticSymmetry.feasible_permute g h.2 h.1
      ⟨h'.2, h'.1⟩
    projection_covariant := QuadraticSymmetry.projection_covariant }

/-- The orthonormal compressed model, with its actual orthogonal action.
The dimension formula requires at least two vertices. -/
def symmetricCompressedModel [Nonempty V] [Nontrivial V] :
    OrthogonalSymmetricModel V (QuadraticOrthogonal.Index V)
      (3 * (Fintype.card V).choose 2 - Fintype.card V) where
  formulation := symmetricCompressed
  order_eq := symmetric_compressed_size
  symmetry := {
    action := QuadraticOrthogonal.orthogonalAction
    slice_preserved := fun g _ h => QuadraticOrthogonal.slice_preserved g h
    feasible_preserved := fun g _ h =>
      let h' := QuadraticOrthogonal.feasible_congruence g h.2 h.1
      ⟨h'.2, h'.1⟩
    projection_covariant := QuadraticOrthogonal.projection_covariant }

@[simp] theorem symmetricRawModel_formulation [Nonempty V] :
    (symmetricRawModel (V := V)).formulation = symmetricRaw := rfl

@[simp] theorem symmetricCompressedModel_formulation [Nonempty V] [Nontrivial V] :
    (symmetricCompressedModel (V := V)).formulation = symmetricCompressed := rfl

/-- Exact symmetric raw formulation of order `3m`, with coherent coordinate permutations. -/
theorem symmetric_raw [Nonempty V] :
    Nonempty (PermutationSymmetricModel V (QuadraticSymmetry.Labels V)
      (3 * (Fintype.card V).choose 2)) := ⟨symmetricRawModel⟩

/-- Exact symmetric compressed formulation of order `3m-n`, with coherent orthogonal congruences. -/
theorem symmetric_compressed [Nonempty V] [Nontrivial V] :
    Nonempty (OrthogonalSymmetricModel V (QuadraticOrthogonal.Index V)
      (3 * (Fintype.card V).choose 2 - Fintype.card V)) := ⟨symmetricCompressedModel⟩

/-- Ordered raw existence only; this does not assert impossibility of symmetry. -/
theorem ordered_raw [Nonempty V] [LinearOrder V] :
    Nonempty (ExactPSDFormulation (QuadraticRaw.Label (QuadraticRaw.orderedRoots (V := V)))
      (TreePolytope V)) ∧
    Fintype.card (QuadraticRaw.Label (QuadraticRaw.orderedRoots (V := V))) =
      2 * (Fintype.card V).choose 2 := ⟨⟨asymmetricRaw⟩, asymmetric_raw_size⟩

/-- Ordered compressed existence of order `2m-1`, for at least two vertices. -/
theorem ordered_compressed [Nonempty V] [LinearOrder V] [OrderBot V] [Nontrivial V] :
    Nonempty (ExactPSDFormulation
      (QuadraticCompression.Kept (QuadraticRaw.orderedRoots (V := V))
        QuadraticOrders.asymmetricDeletion) (TreePolytope V)) ∧
    Fintype.card (QuadraticCompression.Kept (QuadraticRaw.orderedRoots (V := V))
      QuadraticOrders.asymmetricDeletion) = 2 * (Fintype.card V).choose 2 - 1 :=
  asymmetric_quadratic_lift

end
end Lemmata.SpanningTreeSymmetricEF.SDPResults
