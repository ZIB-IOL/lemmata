module

public import Lemmata.RM59.Proof.FieldCoordinates
public import Lemmata.RM59.Proof.FrameGeometry
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Data.Fin.SuccPred
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.FieldRank

open Module
open scoped Matrix

abbrev FieldPoint := TraceGeometry.FieldPoint

instance : FiniteDimensional Field F8Scalar := FieldCoordinates.chunkEquiv.finiteDimensional

theorem scalar_finrank : Module.finrank Field F8Scalar = 3 := by
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    FieldCoordinates.chunkEquiv.finrank_eq.symm

theorem finrank_restrictScalars (S : Submodule F8Scalar FieldPoint) :
    Module.finrank Field (S.restrictScalars Field) = 3 * Module.finrank F8Scalar S := by
  have h := Module.finrank_mul_finrank Field F8Scalar (S.restrictScalars Field)
  rw [scalar_finrank, (S.restrictScalarsEquiv Field).finrank_eq] at h
  exact h.symm

theorem binary_span_rank_le (s : Set FieldPoint) :
    Module.finrank Field (Submodule.span Field s) ≤
      3 * Module.finrank F8Scalar (Submodule.span F8Scalar s) := by
  have hle : Submodule.span Field s ≤ (Submodule.span F8Scalar s).restrictScalars Field := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span hx
  calc
    _ ≤ Module.finrank Field ((Submodule.span F8Scalar s).restrictScalars Field) :=
      Submodule.finrank_mono hle
    _ = _ := finrank_restrictScalars _

theorem card_le_three_span_rank {ι : Type*} [Fintype ι] (v : ι → FieldPoint)
    (hv : LinearIndependent Field v) :
    Fintype.card ι ≤ 3 * Module.finrank F8Scalar (Submodule.span F8Scalar (Set.range v)) := by
  rw [← finrank_span_eq_card hv]
  exact binary_span_rank_le (Set.range v)

theorem exists_field_independent_subfamily {ι : Type*} [Fintype ι]
    (v : ι → FieldPoint) (hv : LinearIndependent Field v) (k : Nat)
    (hk : 3 * (k - 1) < Fintype.card ι) :
    ∃ f : Fin k → ι, LinearIndependent F8Scalar (fun j => v (f j)) := by
  classical
  have hdim := card_le_three_span_rank v hv
  have hkr : k ≤ Module.finrank F8Scalar (Submodule.span F8Scalar (Set.range v)) := by omega
  obtain ⟨g, hgmem, _, hg⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F8Scalar (Set.range v)
  have hgk := hg.comp (Fin.castLE hkr) (Fin.castLE_injective hkr)
  let f : Fin k → ι := fun i => Classical.choose (hgmem (Fin.castLE hkr i))
  have hf : ∀ i, v (f i) = g (Fin.castLE hkr i) :=
    fun i => Classical.choose_spec (hgmem (Fin.castLE hkr i))
  refine ⟨f, ?_⟩
  have heq : (fun i : Fin k => v (f i)) = fun i => g (Fin.castLE hkr i) := funext hf
  rw [heq]
  exact hgk

theorem exists_field_independent_differences {ι : Type*} [Fintype ι]
    (p : ι → FieldPoint) (hp : AffineIndependent Field p) (base : ι) (k : Nat)
    (hk : 3 * (k - 1) < Fintype.card ι - 1) :
    ∃ f : Fin k → ι, LinearIndependent F8Scalar (fun j => p (f j) - p base) := by
  classical
  let v : {i : ι // i ≠ base} → FieldPoint := fun i => p i - p base
  have hv : LinearIndependent Field v :=
    (affineIndependent_iff_linearIndependent_vsub Field p base).mp hp
  have hcard : Fintype.card {i : ι // i ≠ base} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  obtain ⟨f, hf⟩ := exists_field_independent_subfamily v hv k (by simpa only [hcard] using hk)
  exact ⟨fun j => (f j).val, hf⟩

theorem exists_full_frame {ι : Type*} [Fintype ι] (p : ι → FieldPoint)
    (hp : AffineIndependent Field p) (base : ι) (hcard : 6 < Fintype.card ι - 1) :
    ∃ q : Fin 4 → ι, FrameGeometry.frameDeterminant (p ∘ q) ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_field_independent_differences p hp base 3 hcard
  let q : Fin 4 → ι := Fin.cases base f
  refine ⟨q, ?_⟩
  change (FrameGeometry.differenceMatrix (p ∘ q)).det ≠ 0
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  change LinearIndependent F8Scalar (fun j : Fin 3 => p (f j) - p base)
  exact hf

theorem exists_independent_triple {ι : Type*} [Fintype ι] (p : ι → FieldPoint)
    (hp : AffineIndependent Field p) (base : ι) (hcard : 3 < Fintype.card ι - 1) :
    ∃ b c : ι, LinearIndependent F8Scalar ![p b - p base, p c - p base] := by
  obtain ⟨f, hf⟩ := exists_field_independent_differences p hp base 2 hcard
  refine ⟨f 0, f 1, ?_⟩
  have heq : (fun j : Fin 2 => p (f j) - p base) =
      ![p (f 0) - p base, p (f 1) - p base] := by
    funext j
    fin_cases j <;> rfl
  rw [heq] at hf
  exact hf

end Lemmata.RM59.FieldRank
