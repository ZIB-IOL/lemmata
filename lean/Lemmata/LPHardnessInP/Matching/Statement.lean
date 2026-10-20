module

public import Lemmata.LPHardnessInP.Joins.Graph

@[expose] public section

namespace Lemmata.LPHardnessInP.Matching

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- A perfect matching on the fixed complete host: a simple graph in which
every vertex has degree one. Its edge set, rather than an abstract violation
matrix, is the solution. -/
def PerfectMatching := {G : SimpleGraph V // ∀ v, Graph.degree G v = 1}

/-- Odd vertex subsets index the cut objectives. -/
def OddCut := {U : Finset V // Odd U.card}

/-- The number of edges of any perfect matching, written as a real number. -/
noncomputable def halfOrder : ℝ := (Fintype.card V : ℝ) / 2

/-- The positive cut penalty for approximation factor `α`. -/
noncomputable def penalty (α : ℝ) : ℝ := (α - 1) * (Fintype.card V : ℝ)

variable {V}

/-- The concrete odd-cut versus perfect-matching crossing matrix. -/
noncomputable def crossing (U : OddCut V) (M : PerfectMatching V) : ℝ :=
  Graph.cutCount M.val U.val

/-- Positive cut-metric costs, summed over the actual matching edges. -/
noncomputable def matchingValue (α : ℝ) (U : OddCut V) (M : PerfectMatching V) : ℝ :=
  Graph.cost M.val U.val (penalty V α)

/-- The corresponding approximation slack. The optimum formula is proved
for even vertex sets in the accompanying module. -/
noncomputable def matchingSlack (α : ℝ) (U : OddCut V) (M : PerfectMatching V) : ℝ :=
  matchingValue α U M - (halfOrder V + penalty V α) / α

/-- The odd-cut objective with matching-indicator edge weights. -/
noncomputable def oddCutValue (M : PerfectMatching V) (U : OddCut V) : ℝ :=
  Graph.cutCount M.val U.val

end Lemmata.LPHardnessInP.Matching
