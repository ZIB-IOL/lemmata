module

public import Lemmata.LPHardnessInP.Joins.Graph

@[expose] public section

namespace Lemmata.LPHardnessInP.Joins

variable (V : Type*) [Fintype V]

/-- A V-join on the complete host is a simple graph whose odd-degree vertex
set is the full vertex set. -/
def VJoin := {G : SimpleGraph V // ∀ v, Odd (Graph.degree G v)}

end Lemmata.LPHardnessInP.Joins
