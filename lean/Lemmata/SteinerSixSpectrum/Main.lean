module

public import Lemmata.SteinerSixSpectrum.BaseProof
public import Lemmata.SteinerSixSpectrum.SteinerDesign

public section

namespace Lemmata.SteinerSixSpectrum

private theorem exists_nat (n : ℕ) (h : constructible n) :
    Nonempty (SteinerSystem (Fin n)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases constructionCases h with ⟨p, hp⟩ | ⟨p, hp⟩ | checked
    · exact realizeStep hp ih
    · exact realizeProduct hp ih
    · exact checked

-- DOCS_BEGIN_MAIN
theorem steinerSix_exists (n : ℤ)
    (hmod : n % 15 = 1 ∨ n % 15 = 6)
    (horder : 81 < n ∨ n = 31 ∨ n = 66 ∨ n = 76) :
    Nonempty (S(2, 6, n.toNat)) := by
  have hn : 0 ≤ n := by omega
  have cast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  apply Nonempty.map SteinerSystem.toSteinerDesign
  apply exists_nat
  unfold constructible admissible
  constructor <;> omega
-- DOCS_END_MAIN

end Lemmata.SteinerSixSpectrum
