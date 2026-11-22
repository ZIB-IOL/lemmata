module

public import Lemmata.ModifiedE8Bell.Enumeration
public import Lemmata.ModifiedE8Bell.Witness
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- No deterministic strategy pair exceeds the enumerated chamber maximum. -/
theorem fourBell_upper (a b : Signing) : fourBell a b ≤ 24416 := by
  obtain ⟨c,d,heq,hgap⟩ := exists_chamber_pair a b
  rw [← heq]
  calc
    fourBell c d ≤ envelope (sumRoot d) := fourBell_le_envelope c d
    _ = envelope (fun j => 2 * coordinates (gap d) j) := by
      congr 1
      funext j
      exact sumRoot_gap d j
    _ ≤ 24416 := chamber_envelope (gap d) hgap (last_coordinate_le d)

lemma fourBell_neg (a b : Signing) : fourBell (fun i => !(a i)) b = -fourBell a b := by
  have hn (v : Bool) : sign (!v) = -sign v := by cases v <;> rfl
  simp only [fourBell, hn, neg_mul, Finset.sum_neg_distrib]

-- DOCS_BEGIN_MAIN
/-- The modified E₈ Bell matrix has classical value exactly 6104. -/
theorem exact_classical_value : ExactClassicalValue := by
  constructor
  · intro a b
    have hu := fourBell_upper a b
    have hl := fourBell_upper (fun i => !(a i)) b
    rw [fourBell_neg] at hl
    change |(fourBell a b : ℚ) / 4| ≤ 6104
    rw [abs_le]
    have huq : (fourBell a b : ℚ) ≤ 24416 := by exact_mod_cast hu
    have hlq : -(fourBell a b : ℚ) ≤ 24416 := by exact_mod_cast hl
    constructor <;> linarith
  · refine ⟨witnessA,witnessB,?_⟩
    norm_num [bell, witness_value]
-- DOCS_END_MAIN

end Lemmata.ModifiedE8Bell
