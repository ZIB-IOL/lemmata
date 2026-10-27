module

public import Lemmata.CocubicCovering.Proof.Schur
public meta import Lemmata.CocubicCovering.Proof.Schur
public import Lemmata.CocubicCovering.Proof.Symplectic
public meta import Lemmata.CocubicCovering.Proof.Symplectic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringGeometry

open Covering Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

variable {K E Q : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup Q] [Module K Q]

theorem gram_rank_le [FiniteDimensional K E] [FiniteDimensional K Q]
    (B : BilinForm K E) (e : Q →ₗ[K] E) :
    finrank K (LinearMap.range (gram B e)) ≤ finrank K (LinearMap.range B) := by
  have hgram : gram B e = LinearMap.comp e.dualMap (LinearMap.comp B e) := by
    ext x y
    rfl
  calc
    finrank K (LinearMap.range (gram B e)) =
        finrank K ((LinearMap.range (LinearMap.comp B e)).map e.dualMap) := by
      rw [hgram, LinearMap.range_comp]
    _ ≤ finrank K (LinearMap.range (LinearMap.comp B e)) :=
      Submodule.finrank_map_le _ _
    _ ≤ finrank K (LinearMap.range B) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range e B)

theorem gram_isAlt (B : BilinForm K E) (hB : B.IsAlt) (e : Q →ₗ[K] E) :
    (gram B e).IsAlt := fun x => hB (e x)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem matrix_bilinear_kernel (A : Matrix n n K) :
    LinearMap.ker (Matrix.toBilin' A) = LinearMap.ker A.transpose.mulVecLin := by
  ext v
  change Matrix.toBilin' A v = 0 ↔ A.transpose.mulVecLin v = 0
  constructor
  · intro hv
    funext i
    have hi := LinearMap.congr_fun hv (Pi.single i 1)
    simpa [Matrix.toBilin'_apply, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Pi.single_apply, mul_comm] using hi
  · intro hv
    apply (Pi.basisFun K n).ext
    intro i
    have hi := congrFun hv i
    simpa [Pi.basisFun_apply, Matrix.toBilin'_apply, Matrix.mulVecLin_apply, Matrix.mulVec,
      Matrix.vecMul, dotProduct, Pi.single_apply, mul_comm] using hi

theorem matrix_bilinear_rank (A : Matrix n n K) :
    finrank K (LinearMap.range (Matrix.toBilin' A)) = A.rank := by
  have hB := (Matrix.toBilin' A).finrank_range_add_finrank_ker
  have hA := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [matrix_bilinear_kernel] at hB
  calc
    finrank K (LinearMap.range (Matrix.toBilin' A)) = A.transpose.rank := by
      change finrank K (LinearMap.range (Matrix.toBilin' A)) =
        finrank K (LinearMap.range A.transpose.mulVecLin)
      omega
    _ = A.rank := Matrix.rank_transpose A

theorem schur_rank_bound [FiniteDimensional K E] (B : BilinForm K E)
    (e : (m ⊕ n → K) →ₗ[K] E) (A Ai : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix n m K) (D : Matrix n n K)
    (hfull : gram B e = Matrix.toBilin' (Matrix.fromBlocks A X Y D))
    (hleft : Ai * A = 1) (hright : A * Ai = 1) :
    Fintype.card m + (CoveringSchur.schur Ai X Y D).rank ≤
      finrank K (LinearMap.range B) := by
  have hrank : (Matrix.fromBlocks A X Y D).rank ≤ finrank K (LinearMap.range B) := by
    rw [← matrix_bilinear_rank, ← hfull]
    exact gram_rank_le B e
  rwa [CoveringSchur.rank_fromBlocks_of_inverse A Ai X Y D hleft hright] at hrank

def schurInclusion (Ai : Matrix m m K) (X : Matrix m n K) :
    (n → K) →ₗ[K] (m ⊕ n → K) :=
  (LinearEquiv.sumArrowLequivProdArrow m n K K).symm.toLinearMap.comp
    ((-(Ai * X).mulVecLin).prod LinearMap.id)

@[simp] theorem schurInclusion_apply (Ai : Matrix m m K) (X : Matrix m n K) (z : n → K) :
    schurInclusion Ai X z = Sum.elim (-((Ai * X).mulVec z)) z := rfl

theorem schurInclusion_mulVec (A Ai : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix n m K) (D : Matrix n n K) (hright : A * Ai = 1) (z : n → K) :
    (Matrix.fromBlocks A X Y D).mulVec (schurInclusion Ai X z) =
      Sum.elim (0 : m → K) ((CoveringSchur.schur Ai X Y D).mulVec z) := by
  rw [schurInclusion_apply, Matrix.fromBlocks_mulVec]
  have htop : A.mulVec (-((Ai * X).mulVec z)) + X.mulVec z = 0 := by
    simp [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hright]
  have hbottom : Y.mulVec (-((Ai * X).mulVec z)) + D.mulVec z =
      (CoveringSchur.schur Ai X Y D).mulVec z := by
    simp [CoveringSchur.schur, Matrix.sub_mulVec, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.add_mulVec, Matrix.neg_mulVec,
      sub_eq_add_neg, add_comm]
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, htop, hbottom]

theorem schur_pullback (A Ai : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix n m K) (D : Matrix n n K) (hright : A * Ai = 1) :
    gram (Matrix.toBilin' (Matrix.fromBlocks A X Y D)) (schurInclusion Ai X) =
      Matrix.toBilin' (CoveringSchur.schur Ai X Y D) := by
  apply BilinForm.ext
  intro x y
  change Matrix.toBilin' (Matrix.fromBlocks A X Y D)
    (schurInclusion Ai X x) (schurInclusion Ai X y) = _
  rw [Matrix.toBilin'_apply', schurInclusion_mulVec A Ai X Y D hright]
  rw [schurInclusion_apply, Matrix.toBilin'_apply']
  simp [dotProduct, Fintype.sum_sum_type]

theorem schur_isAlt (A Ai : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix n m K) (D : Matrix n n K) (hright : A * Ai = 1)
    (hB : (Matrix.toBilin' (Matrix.fromBlocks A X Y D)).IsAlt) :
    (Matrix.toBilin' (CoveringSchur.schur Ai X Y D)).IsAlt := by
  rw [← schur_pullback A Ai X Y D hright]
  exact gram_isAlt _ hB _

variable {ι κ : Type*} [Fintype ι]

theorem frame_functionals_injective (B : BilinForm K E) (W C : Submodule K E)
    (frame : ι → E) (hmem : ∀ i, frame i ∈ W)
    (hcore : W ⊓ LinearMap.ker B = C)
    (hdisjoint : Submodule.span K (Set.range frame) ⊓ C = ⊥)
    (hindependent : Function.Injective (Fintype.linearCombination K frame)) :
    Function.Injective (LinearMap.comp B (Fintype.linearCombination K frame)) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  let v := (Fintype.linearCombination K frame) a
  have hspan : v ∈ Submodule.span K (Set.range frame) := by
    rw [← Fintype.range_linearCombination K frame]
    exact ⟨a, rfl⟩
  have hW : v ∈ W := (Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hmem i)) hspan
  have hC : v ∈ C := by
    rw [← hcore]
    exact ⟨hW, ha⟩
  have hzero : v = 0 := by
    have hboth : v ∈ Submodule.span K (Set.range frame) ⊓ C := ⟨hspan, hC⟩
    rw [hdisjoint] at hboth
    exact hboth
  exact hindependent (by simpa only [map_zero] using hzero)

def crossPairing (B : BilinForm K E) (frame : ι → E) (outside : κ → E) :
    (ι → K) →ₗ[K] (κ → K) :=
  LinearMap.pi fun j => (B.flip (outside j)).comp (Fintype.linearCombination K frame)

@[simp] theorem crossPairing_apply (B : BilinForm K E) (frame : ι → E)
    (outside : κ → E) (a : ι → K) (j : κ) :
    crossPairing B frame outside a j = B ((Fintype.linearCombination K frame) a) (outside j) := rfl

theorem crossPairing_injective (B : BilinForm K E) (W : Submodule K E)
    (frame : ι → E) (outside : κ → E)
    (hspanning : W ⊔ Submodule.span K (Set.range outside) = ⊤)
    (horthogonal : ∀ i, ∀ w ∈ W, B (frame i) w = 0)
    (hinjective : Function.Injective
      (LinearMap.comp B (Fintype.linearCombination K frame))) :
    Function.Injective (crossPairing B frame outside) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  let v := (Fintype.linearCombination K frame) a
  have hW : W ≤ LinearMap.ker (B v) := by
    intro w hw
    change B ((Fintype.linearCombination K frame) a) w = 0
    simp only [Fintype.linearCombination_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [horthogonal i w hw, mul_zero]
  have houtside : Submodule.span K (Set.range outside) ≤ LinearMap.ker (B v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact congrFun ha j
  have hall : W ⊔ Submodule.span K (Set.range outside) ≤ LinearMap.ker (B v) :=
    sup_le hW houtside
  have hfull : (LinearMap.comp B (Fintype.linearCombination K frame)) a = 0 := by
    ext z
    change B v z = 0
    apply hall
    rw [hspanning]
    exact Submodule.mem_top
  exact hinjective (by simpa only [map_zero] using hfull)

theorem frame_functionals_injective_of_cross (B : BilinForm K E)
    (frame : ι → E) (outside : κ → E)
    (hinjective : Function.Injective (crossPairing B frame outside)) :
    Function.Injective (LinearMap.comp B (Fintype.linearCombination K frame)) := by
  intro a b hab
  apply hinjective
  funext j
  exact LinearMap.congr_fun hab (outside j)

theorem crossPairing_eq_of_pairings (B : BilinForm K E) (D : BilinForm K Q)
    (frame : ι → E) (otherFrame : ι → Q) (outside : κ → E) (otherOutside : κ → Q)
    (hpairings : ∀ i j, D (otherFrame i) (otherOutside j) = B (frame i) (outside j)) :
    crossPairing D otherFrame otherOutside = crossPairing B frame outside := by
  classical
  apply (Pi.basisFun K ι).ext
  intro i
  funext j
  change D ((Fintype.linearCombination K otherFrame) (Pi.single i 1)) (otherOutside j) =
    B ((Fintype.linearCombination K frame) (Pi.single i 1)) (outside j)
  simp only [Fintype.linearCombination_apply_single, one_smul]
  exact hpairings i j

end Lemmata.CocubicCovering.CoveringGeometry
