module

public import Lemmata.Centroid.Proof.General.CentroidBounds
public import Lemmata.Centroid.Proof.General.ProjectionBounds
public import Lemmata.Centroid.Proof.Tensor.SupportProjection
public import Mathlib.LinearAlgebra.Matrix.Bilinear

@[expose] public section

open scoped Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F] {V : Fin 3 → Type*} [∀ i, Fintype (V i)]

def leftFamilyMap (P : ∀ i, Matrix (V i) (V i) F) :
    (∀ i, Matrix (V i) (V i) F) →ₗ[F] (∀ i, Matrix (V i) (V i) F) :=
  LinearMap.pi fun i => (mulLeftLinearMap (V i) F (P i)).comp (LinearMap.proj i)

def rightFamilyMap (P : ∀ i, Matrix (V i) (V i) F) :
    (∀ i, Matrix (V i) (V i) F) →ₗ[F] (∀ i, Matrix (V i) (V i) F) :=
  LinearMap.pi fun i => (mulRightLinearMap (V i) F (P i)).comp (LinearMap.proj i)

def leftIdealFamily (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) :=
  (centroidIdealSpace T hT I).map (leftFamilyMap P)

def rightIdealFamily (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) :=
  (centroidIdealSpace T hT I).map (rightFamilyMap P)

theorem leftIdealFamily_commonKernel (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    let := centroidModule T hT i
    let := centroidModuleScalarTower T hT i
    commonKernel (leftIdealFamily T hT I P) i =
      General.leftProjectedKernel I (P i).mulVecLin := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  ext u
  rw [mem_commonKernel]
  simp only [General.leftProjectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu c
    have he := hu (leftFamilyMap P c.1.1) ⟨c.1.1, ⟨c.1, c.2, rfl⟩, rfl⟩
    change (P i * c.1.1 i) *ᵥ u = 0 at he
    change P i *ᵥ (c.1.1 i *ᵥ u) = 0
    rwa [Matrix.mulVec_mulVec]
  · rintro hu _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change (P i * c.1 i) *ᵥ u = 0
    rw [← Matrix.mulVec_mulVec]
    exact hu ⟨c, hc⟩

theorem rightIdealFamily_commonKernel (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    let := centroidModule T hT i
    let := centroidModuleScalarTower T hT i
    commonKernel (rightIdealFamily T hT I P) i =
      General.rightProjectedKernel I (P i).mulVecLin := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  ext u
  rw [mem_commonKernel]
  simp only [General.rightProjectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu c
    have he := hu (rightFamilyMap P c.1.1) ⟨c.1.1, ⟨c.1, c.2, rfl⟩, rfl⟩
    change (c.1.1 i * P i) *ᵥ u = 0 at he
    change c.1.1 i *ᵥ (P i *ᵥ u) = 0
    rwa [Matrix.mulVec_mulVec]
  · rintro hu _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change (c.1 i * P i) *ᵥ u = 0
    rw [← Matrix.mulVec_mulVec]
    exact hu ⟨c, hc⟩

theorem leftIdealFamily_row_finrank (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : (P i).mulVecLin.ker = commonKernel (centroidIdealSpace T hT I) i) :
    let := centroidModule T hT i
    let := centroidModuleScalarTower T hT i
    let := centroidModuleFaithful T hT i
    Module.finrank F (rowSpace (leftIdealFamily T hT I P) i) =
      Module.finrank F (General.ProjectedModule (centroidAlgebra T hT) (V i → F) I) -
        Module.finrank F (General.projectedKernel (M := V i → F) I) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  let := centroidModuleFaithful T hT i
  have hk : (P i).mulVecLin.ker =
      (General.idealKernel (M := V i → F) I).restrictScalars F := by
    rw [centroidModule_idealKernel]
    exact hP
  have hcod := General.leftProjectedKernel_codim (F := F) (M := V i → F) I (P i).mulVecLin hk
  have hdim := finrank_rowSpace_add_commonKernel (leftIdealFamily T hT I P) i
  rw [leftIdealFamily_commonKernel] at hdim
  rw [Module.finrank_pi] at hcod
  omega

theorem rightIdealFamily_row_finrank_le (T : Tensor F (Fin 3) V) (hT : Concise T)
    (I : Ideal (centroidAlgebra T hT)) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : P i * P i = P i)
    (hrange : (P i).mulVecLin.range =
      commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i) :
    Module.finrank F (rowSpace (rightIdealFamily T hT I P) i) ≤
      Module.finrank F
          (commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i) -
        Module.finrank F (commonKernel (centroidIdealSpace T hT I) i) := by
  let := centroidModule T hT i
  let := centroidModuleScalarTower T hT i
  have hsq : (P i).mulVecLin.comp (P i).mulVecLin = (P i).mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hP]
  have hK : (General.idealKernel (M := V i → F) I).restrictScalars F ≤
      commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i := by
    rw [← centroidModule_idealKernel]
    exact General.idealKernel_antitone inf_le_left
  have hcod := General.rightProjectedKernel_codim_le I
    (commonKernel (centroidIdealSpace T hT (General.annihilatorInIdeal I)) i)
    (P i).mulVecLin hsq hrange hK
  rw [Module.finrank_pi, centroidModule_kernel_finrank] at hcod
  have hdim := finrank_rowSpace_add_commonKernel (rightIdealFamily T hT I P) i
  rw [rightIdealFamily_commonKernel] at hdim
  omega

end Lemmata.Centroid.Tensor
