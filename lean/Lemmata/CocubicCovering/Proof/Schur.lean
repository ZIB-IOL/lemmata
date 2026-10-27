module

public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringSchur

open Module LinearMap Matrix
open scoped BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

def prodSubmoduleEquiv (P : Submodule K (m → K)) (Q : Submodule K (n → K)) :
    P.prod Q ≃ₗ[K] P × Q where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun x := ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_blockDiagonal (A : Matrix m m K) (D : Matrix n n K) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow m n K K
  let f := (Matrix.fromBlocks A 0 0 D).mulVecLin
  let g := A.mulVecLin.prodMap D.mulVecLin
  have hcomp : e.toLinearMap.comp f = g.comp e.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply Prod.ext <;> funext i
    · change ((Matrix.fromBlocks A 0 0 D).mulVecLin v) (Sum.inl i) =
        A.mulVecLin (v ∘ Sum.inl) i
      simp [Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec]
    · change ((Matrix.fromBlocks A 0 0 D).mulVecLin v) (Sum.inr i) =
        D.mulVecLin (v ∘ Sum.inr) i
      simp [Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec]
  have hmap : (LinearMap.range f).map e.toLinearMap = LinearMap.range g := by
    rw [← LinearMap.range_comp, hcomp,
      LinearMap.range_comp_of_range_eq_top g (LinearEquiv.range e)]
  have hd : finrank K (LinearMap.range f) = finrank K (LinearMap.range g) := by
    rw [← hmap, e.finrank_map_eq]
  change finrank K (LinearMap.range f) = _
  rw [hd]
  change finrank K (LinearMap.range (A.mulVecLin.prodMap D.mulVecLin)) = _
  rw [LinearMap.range_prodMap]
  simpa only [Module.finrank_prod, Matrix.rank] using
    (prodSubmoduleEquiv (LinearMap.range A.mulVecLin) (LinearMap.range D.mulVecLin)).finrank_eq

theorem rank_mul_left_of_inverse (L Li : Matrix m m K) (X : Matrix m n K)
    (hL : Li * L = 1) : (L * X).rank = X.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right L X)
  have h := Matrix.rank_mul_le_right Li (L * X)
  rwa [← Matrix.mul_assoc, hL, Matrix.one_mul] at h

theorem rank_mul_right_of_inverse (R Ri : Matrix n n K) (X : Matrix m n K)
    (hR : R * Ri = 1) : (X * R).rank = X.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left X R)
  have h := Matrix.rank_mul_le_left (X * R) Ri
  rwa [Matrix.mul_assoc, hR, Matrix.mul_one] at h

def schur (Ai : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K)
    (D : Matrix n n K) : Matrix n n K := D - C * Ai * B

def leftEliminator (Ai : Matrix m m K) (C : Matrix n m K) : Matrix (m ⊕ n) (m ⊕ n) K :=
  Matrix.fromBlocks 1 0 (-(C * Ai)) 1

def rightEliminator (Ai : Matrix m m K) (B : Matrix m n K) : Matrix (m ⊕ n) (m ⊕ n) K :=
  Matrix.fromBlocks 1 (-(Ai * B)) 0 1

theorem leftEliminator_inverse (Ai : Matrix m m K) (C : Matrix n m K) :
    Matrix.fromBlocks 1 0 (C * Ai) 1 * leftEliminator Ai C = 1 := by
  simp [leftEliminator, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem rightEliminator_inverse (Ai : Matrix m m K) (B : Matrix m n K) :
    rightEliminator Ai B * Matrix.fromBlocks 1 (Ai * B) 0 1 = 1 := by
  simp [rightEliminator, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem elimination (A Ai : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K)
    (D : Matrix n n K) (hleft : Ai * A = 1) (hright : A * Ai = 1) :
    leftEliminator Ai C * Matrix.fromBlocks A B C D * rightEliminator Ai B =
      Matrix.fromBlocks A 0 0 (schur Ai B C D) := by
  have hc : (C * Ai) * A = C := by rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  have hb : A * (Ai * B) = B := by rw [← Matrix.mul_assoc, hright, Matrix.one_mul]
  simp [leftEliminator, rightEliminator, schur, Matrix.fromBlocks_multiply,
    Matrix.neg_mul, Matrix.mul_neg, hc, hb, sub_eq_add_neg, add_comm]

theorem rank_fromBlocks_of_inverse (A Ai : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (D : Matrix n n K) (hleft : Ai * A = 1) (hright : A * Ai = 1) :
    (Matrix.fromBlocks A B C D).rank = Fintype.card m + (schur Ai B C D).rank := by
  have hA : A.rank = Fintype.card m := by
    apply le_antisymm (Matrix.rank_le_card_width A)
    have h := Matrix.rank_mul_le_left A Ai
    rwa [hright, Matrix.rank_one] at h
  have hrank : (Matrix.fromBlocks A 0 0 (schur Ai B C D)).rank =
      (Matrix.fromBlocks A B C D).rank := by
    rw [← elimination A Ai B C D hleft hright,
      rank_mul_right_of_inverse _ _ _ (rightEliminator_inverse Ai B),
      rank_mul_left_of_inverse _ _ _ (leftEliminator_inverse Ai C)]
  rw [← hrank, rank_blockDiagonal, hA]

theorem symmetric_congruence (A Ai : Matrix m m K) (B : Matrix m n K)
    (D : Matrix n n K) (hleft : Ai * A = 1) (hright : A * Ai = 1)
    (hAi : Ai.transpose = Ai) :
    (rightEliminator Ai B).transpose * Matrix.fromBlocks A B B.transpose D *
      rightEliminator Ai B = Matrix.fromBlocks A 0 0 (schur Ai B B.transpose D) := by
  have htranspose : (rightEliminator Ai B).transpose = leftEliminator Ai B.transpose := by
    simp [rightEliminator, leftEliminator, Matrix.fromBlocks_transpose, hAi]
  rw [htranspose]
  exact elimination A Ai B B.transpose D hleft hright

def localVector (u : m → K) : m ⊕ n → K := Sum.elim u 0

theorem localVector_pairing_zero (C : Matrix m n K) (D : Matrix n n K)
    (u v : m → K) :
    Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D)
      (localVector u) (localVector v) = 0 := by
  simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, localVector, Matrix.fromBlocks]

theorem localVector_outside_pairing (C : Matrix m n K) (D : Matrix n n K)
    (u : m → K) (j : n) :
    Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D)
      (localVector u) (Pi.single (Sum.inr j) 1) = ∑ i, u i * C i j := by
  simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, localVector, Matrix.fromBlocks,
    Pi.single_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def crossMatrix (C : Matrix m n K) (u : ι → m → K) (outside : ι → n) : Matrix ι ι K :=
  fun i j => ∑ k, u i k * C k (outside j)

theorem localFrame_linear_pairing (C : Matrix m n K) (D : Matrix n n K)
    (u : ι → m → K) (outside : ι → n) (a : ι → K) (j : ι) :
    Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D)
      (Fintype.linearCombination K (fun i => localVector (u i)) a)
      (Pi.single (Sum.inr (outside j)) 1) = (crossMatrix C u outside).transpose.mulVec a j := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, localVector_outside_pairing,
    Matrix.mulVec, Matrix.transpose_apply, dotProduct, crossMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem localFrame_injective_of_cross_inverse (C : Matrix m n K) (D : Matrix n n K)
    (u : ι → m → K) (outside : ι → n) (Ni : Matrix ι ι K)
    (hinverse : crossMatrix C u outside * Ni = 1) :
    Function.Injective (LinearMap.comp (Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D))
      (Fintype.linearCombination K (fun i => localVector (u i)))) := by
  intro a b hab
  have hcross : (crossMatrix C u outside).transpose.mulVec a =
      (crossMatrix C u outside).transpose.mulVec b := by
    funext j
    rw [← localFrame_linear_pairing C D u outside a j,
      ← localFrame_linear_pairing C D u outside b j]
    exact LinearMap.congr_fun hab (Pi.single (Sum.inr (outside j)) 1)
  have h := congrArg (fun v => Ni.transpose.mulVec v) hcross
  simpa only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hinverse,
    Matrix.transpose_one, Matrix.one_mulVec] using h

theorem localFrame_hypotheses (C : Matrix m n K) (D : Matrix n n K)
    (u : ι → m → K) (outside : ι → n) (Ni : Matrix ι ι K)
    (hinverse : crossMatrix C u outside * Ni = 1) :
    (∀ i j, Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D)
      (localVector (u i)) (localVector (u j)) = 0) ∧
    Function.Injective (LinearMap.comp (Matrix.toBilin' (Matrix.fromBlocks 0 C C.transpose D))
      (Fintype.linearCombination K (fun i => localVector (u i)))) :=
  ⟨fun i j => localVector_pairing_zero C D (u i) (u j),
    localFrame_injective_of_cross_inverse C D u outside Ni hinverse⟩

end Lemmata.CocubicCovering.CoveringSchur
