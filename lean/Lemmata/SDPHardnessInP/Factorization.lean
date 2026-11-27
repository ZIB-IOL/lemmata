module

public import Lemmata.SDPHardnessInP.Statement
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace Lemmata.SDPHardnessInP

open scoped BigOperators

variable {I J K : Type*} [Fintype K] {S : I → J → ℝ}

/-- Independent maps on instances and solutions preserve the factor size. -/
def PSDFactorization.pullback {I' J' : Type*} (F : PSDFactorization S K)
    (f : I' → I) (g : J' → J) :
    PSDFactorization (fun i j => S (f i) (g j)) K where
  row := fun i => F.row (f i)
  col := fun j => F.col (g j)
  row_psd := fun i => F.row_psd (f i)
  col_psd := fun j => F.col_psd (g j)
  trace_eq := fun i j => F.trace_eq (f i) (g j)

/-- Transposition swaps the two families of PSD factors. -/
def PSDFactorization.transpose (F : PSDFactorization S K) :
    PSDFactorization (fun j i => S i j) K where
  row := F.col
  col := F.row
  row_psd := F.col_psd
  col_psd := F.row_psd
  trace_eq := fun j i => (Matrix.trace_mul_comm _ _).trans (F.trace_eq i j)

/-- Multiplication by a nonnegative scalar preserves the factor size. -/
def PSDFactorization.scale (F : PSDFactorization S K) (c : ℝ) (hc : 0 ≤ c) :
    PSDFactorization (fun i j => c * S i j) K where
  row := fun i => c • F.row i
  col := F.col
  row_psd := fun i => (F.row_psd i).smul hc
  col_psd := F.col_psd
  trace_eq := fun i j => by simp [Matrix.smul_mul, Matrix.trace_smul, F.trace_eq]

/-- A direct sum of PSD matrices is PSD. -/
theorem fromBlocks_psd {A : Matrix K K ℝ} {D : Matrix Unit Unit ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.isHermitian.fromBlocks (by simp) hD.isHermitian)
  intro x
  have h₁ := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h₂ := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  simpa [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Function.comp_def] using add_nonneg h₁ h₂

/-- Append a nonnegative scalar row offset using one extra coordinate. -/
def PSDFactorization.addOffset (F : PSDFactorization S K)
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    PSDFactorization (fun i j => S i j + c i) (K ⊕ Unit) where
  row := fun i => Matrix.fromBlocks (F.row i) 0 0 (c i • 1)
  col := fun j => Matrix.fromBlocks (F.col j) 0 0 1
  row_psd := fun i => fromBlocks_psd (F.row_psd i) (Matrix.PosSemidef.one.smul (hc i))
  col_psd := fun j => fromBlocks_psd (F.col_psd j) Matrix.PosSemidef.one
  trace_eq := fun i j => by
    simpa [Matrix.fromBlocks_multiply, Matrix.trace, Matrix.diag,
      Fintype.sum_sum_type] using F.trace_eq i j

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {value : I → J → ℝ} {bound : I → ℝ}

def CertifiedSDP.pullback {I' J' : Type*}
    (C : CertifiedSDP (E := E) value bound K) (f : I' → I) (g : J' → J) :
    CertifiedSDP (E := E) (fun i j => value (f i) (g j)) (fun i => bound (f i)) K where
  pencil := C.pencil
  realization := fun j => C.realization (g j)
  feasible := fun j => C.feasible (g j)
  objective := fun i => C.objective (f i)
  realizes := fun i j => C.realizes (f i) (g j)
  dual := fun i => C.dual (f i)
  dual_psd := fun i => C.dual_psd (f i)
  offset := fun i => C.offset (f i)
  offset_nonneg := fun i => C.offset_nonneg (f i)
  certificate := fun i z => C.certificate (f i) z

/-- Evaluation at feasible solution realizations gives the slack factorization. -/
def certifiedSlackFactorization (C : CertifiedSDP (E := E) value bound K) :
    PSDFactorization (fun i j => value i j - bound i) (K ⊕ Unit) := by
  let F : PSDFactorization
      (fun i j => (C.dual i * C.pencil (C.realization j)).trace) K :=
    ⟨C.dual, fun j => C.pencil (C.realization j), C.dual_psd, C.feasible, fun _ _ => rfl⟩
  have h : (fun i j => value i j - bound i) =
      (fun i j => (C.dual i * C.pencil (C.realization j)).trace + C.offset i) := by
    funext i j
    rw [← C.realizes i j, C.certificate]
  rw [h]
  exact F.addOffset C.offset C.offset_nonneg

end Lemmata.SDPHardnessInP
