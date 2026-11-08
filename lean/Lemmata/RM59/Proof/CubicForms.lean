module

public import Lemmata.RM59.Proof.Model
public meta import Lemmata.RM59.Proof.Model
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.SetTheory.Cardinal.Finite
public meta import Mathlib.Data.Fintype.Perm
public meta import Lean.Elab.Tactic.Decide

@[expose] public section

namespace Lemmata.RM59

abbrev CubicForm := AlternatingMap Field (Point 9) Field (Fin 3)

abbrev IncreasingTriple := {v : Fin 3 → Fin 9 // StrictMono v}

theorem increasingTriple_card : Fintype.card IncreasingTriple = 84 := by
  native_decide

private theorem exists_sorted_permutation :
    ∀ v : Fin 3 → Fin 9, Function.Injective v →
      ∃ σ : Equiv.Perm (Fin 3), StrictMono (v ∘ σ) := by
  native_decide

def cubicCoefficients (f : CubicForm) : IncreasingTriple → Field :=
  fun t => f fun i => Pi.single (t.val i) 1

theorem cubicCoefficients_injective : Function.Injective cubicCoefficients := by
  intro f g h
  apply (Pi.basisFun Field (Fin 9)).ext_alternating
  intro v hv
  simp only [Pi.basisFun_apply]
  obtain ⟨σ, hσ⟩ := exists_sorted_permutation v hv
  have heq := congrFun h ⟨v ∘ σ, hσ⟩
  change f ((fun i => Pi.single (v i) 1) ∘ σ) =
    g ((fun i => Pi.single (v i) 1) ∘ σ) at heq
  rw [f.map_perm, g.map_perm] at heq
  exact smul_left_cancel (Equiv.Perm.sign σ) heq

instance cubicFormFinite : Finite CubicForm :=
  Finite.of_injective cubicCoefficients cubicCoefficients_injective

theorem cubicCoefficientSpace_card : Nat.card (IncreasingTriple → Field) = 2 ^ 84 := by
  change Nat.card (IncreasingTriple → ZMod 2) = 2 ^ 84
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, increasingTriple_card]

theorem cubicForm_card_le : Nat.card CubicForm ≤ 2 ^ 84 := by
  calc
    Nat.card CubicForm ≤ Nat.card (IncreasingTriple → Field) :=
      Nat.card_le_card_of_injective cubicCoefficients cubicCoefficients_injective
    _ = 2 ^ 84 := cubicCoefficientSpace_card

end Lemmata.RM59
