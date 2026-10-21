module

public import Lemmata.TensorRank.Def.Formats
public import Lemmata.TensorRank.Proof.Flattening
public import Lemmata.TensorRank.Proof.Consequence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank

theorem balancedMatrix_diagonal (r n : ℕ) :
    balancedMatrix r n (balancedDiagonal r n) = 1 := by
  ext a b
  simp [balancedMatrix, balancedDiagonal, Matrix.one_apply]

private def wordMatrix {J F : Type*} [CommMonoid F] (A : Matrix J J F) (q : ℕ) :
    Matrix (Fin q → J) (Fin q → J) F := fun u v => ∏ j, A (u j) (v j)

private theorem wordMatrix_mul {J F : Type*} [Fintype J] [CommSemiring F]
    (A B : Matrix J J F) (q : ℕ) : wordMatrix A q * wordMatrix B q = wordMatrix (A * B) q := by
  ext u v
  simp only [Matrix.mul_apply, wordMatrix, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j w => A (u j) w * B w (v j))).symm

private theorem wordMatrix_one {J F : Type*} [DecidableEq J] [CommSemiring F] (q : ℕ) :
    wordMatrix (1 : Matrix J J F) q = 1 := by
  ext u v
  simp [wordMatrix, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

private theorem nonsingular_minor_lower {F I J : Type*} [Field F] [Fintype I]
    [Fintype J] [DecidableEq J] {V : I → Type*} [∀ i, Fintype (V i)]
    (T : Tensor F I V) (S : Finset I) (a : J → Tensor.CutRow V S)
    (b : J → Tensor.CutColumn V S)
    (h : IsUnit ((Tensor.flatten T S).submatrix a b).det) :
    (Fintype.card J : ℝ) ≤ Tensor.asymptoticRank T := by
  let A := (Tensor.flatten T S).submatrix a b
  have hp (q : ℕ) : Fintype.card J ^ q ≤ Tensor.rank (Tensor.power T q) := by
    have hm : (Tensor.flatten (Tensor.power T q) S).submatrix
        (fun u : Fin q → J => fun i j => a (u j) i)
        (fun v : Fin q → J => fun i j => b (v j) i) = wordMatrix A q := by
      ext u v
      change (∏ j, T (fun i => Tensor.joinCut (V := fun i => Fin q → V i) S
        (fun i j => a (u j) i) (fun i j => b (v j) i) i j)) =
          ∏ j, T (Tensor.joinCut S (a (u j)) (b (v j)))
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      funext i
      by_cases hi : i ∈ S <;> simp [Tensor.joinCut, hi]
    have hi : wordMatrix A q * wordMatrix A⁻¹ q = 1 := by
      rw [wordMatrix_mul, Matrix.mul_nonsing_inv _ h, wordMatrix_one]
    have hr : Fintype.card (Fin q → J) ≤ (wordMatrix A q).rank := by
      calc
        _ = (1 : Matrix (Fin q → J) (Fin q → J) F).rank := Matrix.rank_one.symm
        _ = (wordMatrix A q * wordMatrix A⁻¹ q).rank := by rw [hi]
        _ ≤ _ := Matrix.rank_mul_le_left _ _
    have hminor := Matrix.rank_submatrix_le (Tensor.flatten (Tensor.power T q) S)
      (fun u : Fin q → J => fun i j => a (u j) i)
      (fun v : Fin q → J => fun i j => b (v j) i)
    rw [hm] at hminor
    have hr' : Fintype.card J ^ q ≤ (wordMatrix A q).rank := by simpa using hr
    exact hr'.trans (hminor.trans (Tensor.flatRank_le_rank _ S))
  apply le_ciInf
  intro q
  have hq : (Fintype.card J : ℝ) ^ (q + 1) ≤ (Tensor.rank (Tensor.power T (q + 1)) : ℝ) := by
    exact_mod_cast hp (q + 1)
  have hpos : (0 : ℝ) < q + 1 := by positivity
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (Fintype.card J : ℝ) ^ (q + 1))
    hq (inv_nonneg.mpr hpos.le)
  have he : ((Fintype.card J : ℝ) ^ (q + 1)) ^ ((q + 1 : ℝ)⁻¹) = Fintype.card J := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    simp only [Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ hpos.ne', Real.rpow_one]
  rw [he] at hr
  exact hr

theorem balanced_nonsingular_lower (r n : ℕ) (T : Cubical (r + r) n)
    (hT : (balancedMatrix r n T).det ≠ 0) :
    (n : ℝ) ^ r ≤ Tensor.asymptoticRank T := by
  let S : Finset (Fin (r + r)) := Finset.univ.filter (fun j => j.val < r)
  let a (w : Fin r → Fin n) : Tensor.CutRow (fun _ : Fin (r + r) => Fin n) S :=
    fun j => w ⟨j.val.val, (Finset.mem_filter.mp j.property).2⟩
  let b (w : Fin r → Fin n) : Tensor.CutColumn (fun _ : Fin (r + r) => Fin n) S :=
    fun j => w ⟨j.val.val - r, by
      have hj := j.val.isLt
      omega⟩
  have h : (Tensor.flatten T S).submatrix a b = balancedMatrix r n T := by
    ext u v
    change T (Tensor.joinCut S (a u) (b v)) = T (Fin.addCases u v)
    congr 1
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [Tensor.joinCut, S, a, i.isLt]
    · simp [Tensor.joinCut, S, b]
  have hi : IsUnit ((Tensor.flatten T S).submatrix a b).det := by
    rw [h]
    exact isUnit_iff_ne_zero.mpr hT
  simpa using nonsingular_minor_lower T S a b hi

theorem balancedDiagonal_lower (r n : ℕ) :
    (n : ℝ) ^ r ≤ Tensor.asymptoticRank (balancedDiagonal r n) := by
  apply balanced_nonsingular_lower
  rw [balancedMatrix_diagonal, Matrix.det_one]
  exact one_ne_zero

theorem evenCubicalMaximum_of_squareRoot (hs : SquareRootBound) : EvenCubicalMaximum := by
  intro r n hr
  have hupper (T : Cubical (r + r) n) : Tensor.asymptoticRank T ≤ (n : ℝ) ^ r := by
    have h := cubical_of_squareRoot hs (r + r) n (by omega) T
    rw [← Real.rpow_natCast]
    convert h using 1
    congr 1
    push_cast
    ring
  refine ⟨⟨balancedDiagonal r n, le_antisymm (hupper _) (balancedDiagonal_lower r n)⟩, ?_⟩
  rintro x ⟨T, rfl⟩
  exact hupper T

theorem evenCubicalNonsingular_of_squareRoot (hs : SquareRootBound) : EvenCubicalNonsingular := by
  intro r n hr T hT
  apply le_antisymm
  · have h := cubical_of_squareRoot hs (r + r) n (by omega) T
    rw [← Real.rpow_natCast]
    convert h using 1
    congr 1
    push_cast
    ring
  · exact balanced_nonsingular_lower r n T hT

end Lemmata.TensorRank
