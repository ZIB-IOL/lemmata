module

public import Lemmata.Centroid.Proof.General.BalancedAlgebra
public import Lemmata.Centroid.Proof.General.ProjectedFamilies

@[expose] public section

open scoped Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)
variable (f : A →ₐ[F] centroidAlgebra T hT)

def leftFamily (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) :=
  (idealSpace T hT f I).map (leftFamilyMap P)

def rightFamily (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) :=
  (idealSpace T hT f I).map (rightFamilyMap P)

theorem leftFamily_commonKernel (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    commonKernel (leftFamily T hT f I P) i =
      General.leftProjectedKernel I (P i).mulVecLin := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  ext u
  rw [mem_commonKernel]
  simp only [General.leftProjectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu c
    have he := hu (leftFamilyMap P (f c.1).val) ⟨(f c.1).val, ⟨c.1, c.2, rfl⟩, rfl⟩
    change (P i * (f c.1).val i) *ᵥ u = 0 at he
    change P i *ᵥ ((f c.1).val i *ᵥ u) = 0
    rwa [Matrix.mulVec_mulVec]
  · rintro hu _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change (P i * (f c).val i) *ᵥ u = 0
    rw [← Matrix.mulVec_mulVec]
    exact hu ⟨c, hc⟩

theorem rightFamily_commonKernel (I : Ideal A) (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    commonKernel (rightFamily T hT f I P) i =
      General.rightProjectedKernel I (P i).mulVecLin := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  ext u
  rw [mem_commonKernel]
  simp only [General.rightProjectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu c
    have he := hu (rightFamilyMap P (f c.1).val) ⟨(f c.1).val, ⟨c.1, c.2, rfl⟩, rfl⟩
    change ((f c.1).val i * P i) *ᵥ u = 0 at he
    change (f c.1).val i *ᵥ (P i *ᵥ u) = 0
    rwa [Matrix.mulVec_mulVec]
  · rintro hu _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change ((f c).val i * P i) *ᵥ u = 0
    rw [← Matrix.mulVec_mulVec]
    exact hu ⟨c, hc⟩

theorem leftFamily_row_finrank (hf : Function.Injective f) (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : (P i).mulVecLin.ker = commonKernel (idealSpace T hT f I) i) :
    let := legModule T hT f i
    let := legScalarTower T hT f i
    let := legFaithful T hT f hf i
    Module.finrank F (rowSpace (leftFamily T hT f I P) i) =
      Module.finrank F (General.ProjectedModule A (V i → F) I) -
        Module.finrank F (General.projectedKernel (M := V i → F) I) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  let := legFaithful T hT f hf i
  have hk : (P i).mulVecLin.ker = (General.idealKernel (M := V i → F) I).restrictScalars F := by
    rw [leg_idealKernel]
    exact hP
  have hcod := General.leftProjectedKernel_codim (F := F) (M := V i → F) I (P i).mulVecLin hk
  have hdim := finrank_rowSpace_add_commonKernel (leftFamily T hT f I P) i
  rw [leftFamily_commonKernel] at hdim
  rw [Module.finrank_pi] at hcod
  omega

theorem rightFamily_row_finrank_le (I : Ideal A)
    (P : ∀ i, Matrix (V i) (V i) F) (i : Fin 3)
    (hP : P i * P i = P i)
    (hrange : (P i).mulVecLin.range = commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i) :
    Module.finrank F (rowSpace (rightFamily T hT f I P) i) ≤
      Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i) -
        Module.finrank F (commonKernel (idealSpace T hT f I) i) := by
  let := legModule T hT f i
  let := legScalarTower T hT f i
  have hsq : (P i).mulVecLin.comp (P i).mulVecLin = (P i).mulVecLin := by
    rw [← Matrix.mulVecLin_mul, hP]
  have hK : (General.idealKernel (M := V i → F) I).restrictScalars F ≤
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i := by
    rw [← leg_idealKernel]
    exact General.idealKernel_antitone inf_le_left
  have hcod := General.rightProjectedKernel_codim_le I
    (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i)
    (P i).mulVecLin hsq hrange hK
  rw [Module.finrank_pi, leg_kernel_finrank] at hcod
  have hdim := finrank_rowSpace_add_commonKernel (rightFamily T hT f I P) i
  rw [rightFamily_commonKernel] at hdim
  omega

end Lemmata.Centroid.Tensor.BalancedAlgebra
