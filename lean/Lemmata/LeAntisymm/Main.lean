module

public import Mathlib.Order.Basic

public section

namespace Lemmata.LeAntisymm

-- DOCS_BEGIN_MAIN
/-- In a partial order, two elements below each other are equal. -/
theorem le_antisymm' {α : Type*} [PartialOrder α] {a b : α} (hab : a ≤ b) (hba : b ≤ a) :
    a = b :=
  le_antisymm hab hba

/-- Consequently `≤` determines equality: `a = b` iff each is below the other. -/
theorem eq_iff_le_and_ge {α : Type*} [PartialOrder α] {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h => h ▸ ⟨le_rfl, le_rfl⟩, fun ⟨h₁, h₂⟩ => le_antisymm' h₁ h₂⟩
-- DOCS_END_MAIN

end Lemmata.LeAntisymm
