module

public import Lemmata.LPHardnessInP.RankReduction.Statement
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Lemmata.LPHardnessInP.RankReduction

open Lemmata.SpanningTreeMinSplit
open scoped BigOperators

variable {I J I' J' : Type*}
variable {M N S A B : I → J → ℝ} {T : I' → J' → ℝ}
variable {k l a b : ℕ}

/-- Reindex a finite family of rank-one summands by `Fin`. -/
noncomputable def factorOfFinite {K : Type*} [Fintype K]
    (u : K → I → ℝ) (v : K → J → ℝ)
    (hu : ∀ t i, 0 ≤ u t i) (hv : ∀ t j, 0 ≤ v t j)
    (h : ∀ i j, M i j = ∑ t, u t i * v t j) :
    NonnegativeFactorization M (Fintype.card K) where
  left t := u ((Fintype.equivFin K).symm t)
  right t := v ((Fintype.equivFin K).symm t)
  left_nonneg t i := hu _ _
  right_nonneg t j := hv _ _
  reconstruct i j := by
    rw [h]
    exact ((Fintype.equivFin K).symm.sum_comp (fun t => u t i * v t j)).symm

/-- Restricting or repeating rows and columns never increases the factor count. -/
def factorPullback (F : NonnegativeFactorization T k) (f : I → I') (g : J → J') :
    NonnegativeFactorization (fun i j => T (f i) (g j)) k where
  left t i := F.left t (f i)
  right t j := F.right t (g j)
  left_nonneg t i := F.left_nonneg t (f i)
  right_nonneg t j := F.right_nonneg t (g j)
  reconstruct i j := F.reconstruct (f i) (g j)

/-- Transposition exchanges the two sides of every rank-one summand. -/
def factorTranspose (F : NonnegativeFactorization M k) :
    NonnegativeFactorization (fun j i => M i j) k where
  left := F.right
  right := F.left
  left_nonneg := F.right_nonneg
  right_nonneg := F.left_nonneg
  reconstruct j i := by simpa only [mul_comm] using F.reconstruct i j

/-- Multiplication by a nonnegative row function preserves the factor count. -/
def factorRowScale (F : NonnegativeFactorization M k)
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    NonnegativeFactorization (fun i j => c i * M i j) k where
  left t i := c i * F.left t i
  right := F.right
  left_nonneg t i := mul_nonneg (hc i) (F.left_nonneg t i)
  right_nonneg := F.right_nonneg
  reconstruct i j := by
    rw [F.reconstruct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

/-- Concatenating two finite families of factors gives a factorization of
their sum, including when either family is empty. -/
noncomputable def factorAdd (F : NonnegativeFactorization M k)
    (G : NonnegativeFactorization N l) :
    NonnegativeFactorization (fun i j => M i j + N i j) (k + l) := by
  let u : Fin k ⊕ Fin l → I → ℝ := Sum.elim F.left G.left
  let v : Fin k ⊕ Fin l → J → ℝ := Sum.elim F.right G.right
  have hu : ∀ t i, 0 ≤ u t i := by
    rintro (t | t) i
    · exact F.left_nonneg _ _
    · exact G.left_nonneg _ _
  have hv : ∀ t j, 0 ≤ v t j := by
    rintro (t | t) j
    · exact F.right_nonneg _ _
    · exact G.right_nonneg _ _
  have h : ∀ i j, M i j + N i j = ∑ t, u t i * v t j := by
    intro i j
    simp only [Fintype.sum_sum_type, u, v, Sum.elim_inl, Sum.elim_inr,
      ← F.reconstruct, ← G.reconstruct]
  simpa only [Fintype.card_sum, Fintype.card_fin] using factorOfFinite u v hu hv h

/-- Pairing two families of factors gives a factorization of the entrywise
product with the product of their sizes. -/
noncomputable def factorHadamard (F : NonnegativeFactorization M k)
    (G : NonnegativeFactorization N l) :
    NonnegativeFactorization (fun i j => M i j * N i j) (k * l) := by
  let u : Fin k × Fin l → I → ℝ := fun t i => F.left t.1 i * G.left t.2 i
  let v : Fin k × Fin l → J → ℝ := fun t j => F.right t.1 j * G.right t.2 j
  have hu : ∀ t i, 0 ≤ u t i := fun t i =>
    mul_nonneg (F.left_nonneg t.1 i) (G.left_nonneg t.2 i)
  have hv : ∀ t j, 0 ≤ v t j := fun t j =>
    mul_nonneg (F.right_nonneg t.1 j) (G.right_nonneg t.2 j)
  have h : ∀ i j, M i j * N i j = ∑ t, u t i * v t j := by
    intro i j
    rw [F.reconstruct, G.reconstruct, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    dsimp [u, v]
    ring
  simpa only [Fintype.card_prod, Fintype.card_fin] using factorOfFinite u v hu hv h

/-- A nonnegative row-constant matrix has a one-term factorization. -/
def factorRowConstant (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    NonnegativeFactorization (fun i (_ : J) => c i) 1 where
  left _ i := c i
  right _ _ := 1
  left_nonneg _ i := hc i
  right_nonneg _ _ := zero_le_one
  reconstruct i j := by simp

/-- Adding a nonnegative row offset costs at most one additional factor. -/
noncomputable def factorRowOffset (F : NonnegativeFactorization M k)
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    NonnegativeFactorization (fun i j => M i j + c i) (k + 1) :=
  factorAdd F (factorRowConstant c hc)

/-- The zero matrix has a factorization with no summands. -/
def factorZero : NonnegativeFactorization (fun (_ : I) (_ : J) => (0 : ℝ)) 0 where
  left := Fin.elim0
  right := Fin.elim0
  left_nonneg t := Fin.elim0 t
  right_nonneg t := Fin.elim0 t
  reconstruct i j := by simp

/-- Construct the source factors from the reduction identity. -/
noncomputable def factorReduction
    (FA : NonnegativeFactorization A a) (FT : NonnegativeFactorization T k)
    (FB : NonnegativeFactorization B b) (f : I → I') (g : J → J')
    (h : ReductionIdentity S A B T f g) :
    NonnegativeFactorization S (a * k + b) := by
  have heq : S = fun i j => A i j * T (f i) (g j) + B i j :=
    funext (fun i => funext (h i))
  rw [heq]
  exact factorAdd (factorHadamard FA (factorPullback FT f g)) FB

-- DOCS_BEGIN_MAIN
/-- Nonnegative factorizations compose with a nonnegative multiplier and
remainder: the source uses at most `a * k + b` factors. -/
theorem factorization_reduction (f : I → I') (g : J → J')
    (h : ReductionIdentity S A B T f g) :
    FactorizationReduction S A B T f g := by
  intro a k b FA FT FB
  exact ⟨factorReduction FA FT FB f g h⟩

/-- Every source factor-count lower bound transfers through the reduction. -/
theorem lower_bound_transfer (f : I → I') (g : J → J')
    (h : ReductionIdentity S A B T f g)
    (FA : NonnegativeFactorization A a) (FT : NonnegativeFactorization T k)
    (FB : NonnegativeFactorization B b)
    {L : ℕ} (hL : FactorizationLowerBound S L) :
    L ≤ a * k + b :=
  hL _ (factorReduction FA FT FB f g h)

/-- A uniform factor-count-preserving construction implies rank monotonicity.
This proof also treats matrices without a finite factorization. -/
theorem rank_mono_of_transfer
    (h : ∀ k, NonnegativeFactorization N k → NonnegativeFactorization M k) :
    nonnegativeRank M ≤ nonnegativeRank N := by
  apply le_sInf
  rintro _ ⟨k, rfl, ⟨F⟩⟩
  exact nonnegativeRank_le (h k F)

/-- Pullback monotonicity of nonnegative rank. -/
theorem rank_pullback_le (f : I → I') (g : J → J') :
    nonnegativeRank (fun i j => T (f i) (g j)) ≤ nonnegativeRank T := by
  apply le_sInf
  rintro _ ⟨k, rfl, ⟨F⟩⟩
  exact nonnegativeRank_le (factorPullback F f g)

/-- Nonnegative rank is invariant under transposition. -/
theorem rank_transpose (M : I → J → ℝ) :
    nonnegativeRank (fun j i => M i j) = nonnegativeRank M := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨k, rfl, ⟨F⟩⟩
    exact nonnegativeRank_le (factorTranspose F)
  · apply le_sInf
    rintro _ ⟨k, rfl, ⟨F⟩⟩
    exact nonnegativeRank_le (factorTranspose F)

/-- Nonnegative rank is invariant under strictly positive row scaling. -/
theorem rank_rowScale_eq (M : I → J → ℝ) (c : I → ℝ) (hc : ∀ i, 0 < c i) :
    nonnegativeRank (fun i j => c i * M i j) = nonnegativeRank M := by
  apply le_antisymm
  · exact rank_mono_of_transfer (fun _ F => factorRowScale F c (fun i => (hc i).le))
  · apply rank_mono_of_transfer
    intro k F
    have G := factorRowScale F (fun i => (c i)⁻¹) (fun i => inv_nonneg.mpr (hc i).le)
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hc _)), one_mul] using G

/-- A lower bound against every factorization is equivalent to a
nonnegative-rank lower bound. -/
theorem factorizationLowerBound_iff {L : ℕ} :
    FactorizationLowerBound M L ↔ (L : ℕ∞) ≤ nonnegativeRank M := by
  constructor
  · intro h
    apply le_sInf
    rintro _ ⟨k, rfl, ⟨F⟩⟩
    exact_mod_cast h k F
  · intro h k F
    have h' := h.trans (nonnegativeRank_le F)
    exact_mod_cast h'

/-- The reduction bound stated directly as a nonnegative-rank upper bound. -/
theorem rank_reduction_le (f : I → I') (g : J → J')
    (h : ReductionIdentity S A B T f g)
    (FA : NonnegativeFactorization A a) (FT : NonnegativeFactorization T k)
    (FB : NonnegativeFactorization B b) :
    nonnegativeRank S ≤ ((a * k + b : ℕ) : ℕ∞) :=
  nonnegativeRank_le (factorReduction FA FT FB f g h)

/-- Whenever a finite factorization exists, the nonnegative rank is attained. -/
theorem exists_minimal_factorization (F : NonnegativeFactorization M k) :
    ∃ r : ℕ, nonnegativeRank M = r ∧ Nonempty (NonnegativeFactorization M r) := by
  let s : Set ℕ∞ := {r | ∃ k : ℕ, r = k ∧ Nonempty (NonnegativeFactorization M k)}
  have hs : s.Nonempty := ⟨(k : ℕ∞), k, rfl, ⟨F⟩⟩
  exact csInf_mem hs

/-- The usual rank inequality, with finite factorizations supplied only to
ensure that each of the three ranks is finite. Their sizes need not be optimal. -/
theorem rank_reduction (f : I → I') (g : J → J')
    (h : ReductionIdentity S A B T f g)
    (FA : NonnegativeFactorization A a) (FT : NonnegativeFactorization T k)
    (FB : NonnegativeFactorization B b) :
    nonnegativeRank S ≤
      nonnegativeRank A * nonnegativeRank T + nonnegativeRank B := by
  obtain ⟨a', ha', ⟨FA'⟩⟩ := exists_minimal_factorization FA
  obtain ⟨k', hk', ⟨FT'⟩⟩ := exists_minimal_factorization FT
  obtain ⟨b', hb', ⟨FB'⟩⟩ := exists_minimal_factorization FB
  rw [ha', hk', hb']
  exact_mod_cast rank_reduction_le f g h FA' FT' FB'
-- DOCS_END_MAIN

end Lemmata.LPHardnessInP.RankReduction
