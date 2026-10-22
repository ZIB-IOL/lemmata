module

public import Lemmata.Centroid.Proof.Centroid
public import Lemmata.Centroid.Def.Bounds
public import Lemmata.Centroid.Proof.Linear.SpanBudget
public import Lemmata.Centroid.Proof.Linear.LocalAlgebra
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

theorem centroid_quadratic_bound {T : Tensor F (Fin 3) V} (hT : Concise T) (i : Fin 3) :
    Module.finrank F (centroid T) ≤ (Fintype.card (V i) + 1) ^ 2 / 4 := by
  classical
  have h := Lemmata.Centroid.Linear.commutative_algebra_dimension_bound
    (centroidRepresentation T hT i) (centroidRepresentation_injective hT i)
  calc
    _ = Module.finrank F (centroidAlgebra T hT) :=
      (centroidAlgebra T hT).toSubmoduleEquiv.finrank_eq
    _ ≤ _ := by simpa only [Module.finrank_pi] using h

theorem centroid_artinian (T : Tensor F (Fin 3) V) (hT : Concise T) :
    IsArtinianRing (centroidAlgebra T hT) := by
  classical
  exact isArtinian_of_tower F inferInstance

noncomputable def centroidLocalDecomposition (T : Tensor F (Fin 3) V) (hT : Concise T) :
    centroidAlgebra T hT ≃ₐ[F]
      ∀ m : MaximalSpectrum (centroidAlgebra T hT),
        centroidAlgebra T hT ⧸ m.asIdeal ^ Lemmata.Centroid.Linear.localExponent (centroidAlgebra T hT) := by
  classical
  letI := centroid_artinian T hT
  exact Lemmata.Centroid.Linear.localDecomposition

end Lemmata.Centroid.Tensor
