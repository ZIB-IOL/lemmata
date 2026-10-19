module

public import Lemmata.Shared.Basic
public import Lemmata.SelfImplication.Main
public import Mathlib.Order.Basic

public section

namespace Lemmata.ImplicationComposition

open Lemmata.SelfImplication

-- DOCS_BEGIN_MAIN
/-- Implications compose. -/
theorem implication_composition {P Q R : Prop} (hpq : P → Q) (hqr : Q → R) : P → R :=
  fun hp => Lemmata.Shared.mp hqr (Lemmata.Shared.mp hpq hp)

/-- Composing with self-implication changes nothing; this uses the other contribution. -/
theorem compose_self {P Q : Prop} (hpq : P → Q) : P → Q :=
  implication_composition (self_implication P) hpq
-- DOCS_END_MAIN

/-- On a preorder, transitivity of `≤` is composition of the two inequalities. -/
theorem le_compose {α : Type*} [Preorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  le_trans h₁ h₂

end Lemmata.ImplicationComposition
