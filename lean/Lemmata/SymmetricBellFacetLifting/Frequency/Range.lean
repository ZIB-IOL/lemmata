module

public import Mathlib.Tactic.FinCases
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap1
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap2
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap3
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap4
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap5
public import Lemmata.SymmetricBellFacetLifting.Frequency.Gap6

@[expose] public section

namespace Lemmata.SymmetricBellFacetLifting.Frequency

private theorem oddGaps (i : Fin 38) : ExactGap (17+2*i.val) := by
  fin_cases i
  · exact gap17
  · exact gap19
  · exact gap21
  · exact gap23
  · exact gap25
  · exact gap27
  · exact gap29
  · exact gap31
  · exact gap33
  · exact gap35
  · exact gap37
  · exact gap39
  · exact gap41
  · exact gap43
  · exact gap45
  · exact gap47
  · exact gap49
  · exact gap51
  · exact gap53
  · exact gap55
  · exact gap57
  · exact gap59
  · exact gap61
  · exact gap63
  · exact gap65
  · exact gap67
  · exact gap69
  · exact gap71
  · exact gap73
  · exact gap75
  · exact gap77
  · exact gap79
  · exact gap81
  · exact gap83
  · exact gap85
  · exact gap87
  · exact gap89
  · exact gap91

private theorem evenGaps (i : Fin 32) : ExactGap (28+2*i.val) := by
  fin_cases i
  · exact gap28
  · exact gap30
  · exact gap32
  · exact gap34
  · exact gap36
  · exact gap38
  · exact gap40
  · exact gap42
  · exact gap44
  · exact gap46
  · exact gap48
  · exact gap50
  · exact gap52
  · exact gap54
  · exact gap56
  · exact gap58
  · exact gap60
  · exact gap62
  · exact gap64
  · exact gap66
  · exact gap68
  · exact gap70
  · exact gap72
  · exact gap74
  · exact gap76
  · exact gap78
  · exact gap80
  · exact gap82
  · exact gap84
  · exact gap86
  · exact gap88
  · exact gap90

/-- Strict real convex-hull separation for the closed profiles at all 38 odd
setting counts from 17 to 91 inclusive. -/
theorem oddRange_outside (i : Fin 38) :
    realProfile (reducedShifted (17+2*i.val)) ∉ signedHull (reducedCandidate (17+2*i.val)) :=
  reduced_outside _ (oddGaps i)

/-- Strict real convex-hull separation for the closed profiles at all 32 even
setting counts from 28 to 90 inclusive. -/
theorem evenRange_outside (i : Fin 32) :
    realProfile (reducedShifted (28+2*i.val)) ∉ signedHull (reducedCandidate (28+2*i.val)) :=
  reduced_outside _ (evenGaps i)

end Lemmata.SymmetricBellFacetLifting.Frequency
