module

public import Lemmata.SteinerSixSpectrum.FiniteRouting
public import Lemmata.SteinerSixSpectrum.Orders1To796
public import Lemmata.SteinerSixSpectrum.Orders801To1021
public import Lemmata.SteinerSixSpectrum.Orders1036To1141
public import Lemmata.SteinerSixSpectrum.Orders1146To1296
public import Lemmata.SteinerSixSpectrum.Orders1396To1486
public import Lemmata.SteinerSixSpectrum.Orders1516To1576
import all Lemmata.SteinerSixSpectrum.KernelCertificates

public section

namespace Lemmata.SteinerSixSpectrum

private theorem finiteDesigns : Supplies Routing.terminalOrders := by
  have inventory : Routing.terminalOrders =
      orders1To796Orders ++
      orders801To1021Orders ++
      orders1036To1141Orders ++
      orders1146To1296Orders ++
      orders1396To1486Orders ++
      orders1516To1576Orders := by
    decide +kernel
  rw [inventory]
  have through1021 := suppliesAppend orders1To796 orders801To1021
  have through1141 := suppliesAppend through1021 orders1036To1141
  have through1296 := suppliesAppend through1141 orders1146To1296
  have through1486 := suppliesAppend through1296 orders1396To1486
  exact suppliesAppend through1486 orders1516To1576

theorem constructionCases {n : ℕ} (h : constructible n) :
    (∃ p, stepValid n p) ∨ (∃ p, productValid n p) ∨ Nonempty (SteinerSystem (Fin n)) := by
  by_cases hn : n < 8726
  · rcases Routing.finiteRoute hn h with weight | product | terminal
    · exact Or.inl weight
    · exact Or.inr (Or.inl product)
    · exact Or.inr (Or.inr (finiteDesigns n terminal))
  · exact Or.inl (reduceLarge (by omega) h)

end Lemmata.SteinerSixSpectrum
