module

public import Lemmata.CocubicCovering.Def.Field
public meta import Lemmata.CocubicCovering.Def.Field
public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringBranching

open Module
open scoped BigOperators

abbrev LocalVector := Vector 12

def combine {d : ℕ} (h : Fin d → LocalVector) : Vector d →ₗ[Field] LocalVector :=
  Fintype.linearCombination Field h

@[simp] theorem combine_apply {d : ℕ} (h : Fin d → LocalVector) (b : Vector d) :
    combine h b = ∑ i, b i • h i := rfl

def familySpace {d : ℕ} (h : Fin d → LocalVector) : Submodule Field LocalVector :=
  Submodule.span Field (Set.range h)

@[simp] theorem range_combine {d : ℕ} (h : Fin d → LocalVector) :
    LinearMap.range (combine h) = familySpace h :=
  Fintype.range_linearCombination Field h

def branches (d : ℕ) : Finset (Vector d) := Finset.univ.erase 0

@[simp] theorem mem_branches {d : ℕ} (b : Vector d) :
    b ∈ branches d ↔ b ≠ 0 := by
  simp [branches]

theorem card_branches (d : ℕ) : (branches d).card = 2 ^ d - 1 := by
  simp [branches, Vector, Field]

/-- If the current core is too small, one of the finite branches extends it inside the kernel. -/
theorem exists_kernel_branch {d k : ℕ} (h : Fin d → LocalVector)
    (R K C : Submodule Field LocalVector)
    (hHR : familySpace h ≤ R) (hKR : K ≤ R) (hCK : C ≤ K)
    (hHC : familySpace h ⊓ C = ⊥)
    (hH : finrank Field (familySpace h) = d) (hK : k ≤ finrank Field K)
    (hR : finrank Field R < d + k) :
    ∃ b ∈ branches d, combine h b ∈ K ∧ combine h b ∉ C ∧
      C ⊔ Submodule.span Field {combine h b} ≤ K := by
  have hdim : finrank Field R <
      finrank Field (familySpace h) + finrank Field K := by omega
  obtain ⟨v, hvH, hvK, hv0, hvC⟩ :=
    Covering.exists_new_kernel_direction R (familySpace h) K C hHR hKR hHC hdim
  have hvrange : v ∈ LinearMap.range (combine h) := by
    rw [range_combine]
    exact hvH
  obtain ⟨b, hb⟩ := hvrange
  have hb0 : b ≠ 0 := by
    intro hz
    apply hv0
    rw [← hb, hz, map_zero]
  refine ⟨b, (mem_branches b).mpr hb0, ?_, ?_, ?_⟩
  · simpa only [hb] using hvK
  · simpa only [hb] using hvC
  · apply sup_le hCK
    apply Submodule.span_le.mpr
    intro x hx
    have hxv : x = combine h b := Set.mem_singleton_iff.mp hx
    rw [hxv, hb]
    exact hvK

end Lemmata.CocubicCovering.CoveringBranching
