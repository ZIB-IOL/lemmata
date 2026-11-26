module

public import Lemmata.FrankWolfe.Polytope.Faces
public import Lemmata.FrankWolfe.Statement
public import Lemmata.FrankWolfe.Proof.Interfaces

@[expose] public section

/-!
# Frank–Wolfe: the core

Each theorem proves the proposition of the same name in `Statement.lean`. The proofs are in
`Proof/`.
-/

namespace Lemmata.FrankWolfe

-- DOCS_BEGIN_MAIN
/-- The gap inequalities: primal gap ≤ dual gap ≤ Frank–Wolfe gap. -/
theorem gap_inequalities : GapInequalities := Proof.gap_inequalities

/-- The descent lemma for an `L`-smooth function. -/
theorem descent_lemma : DescentLemma := Proof.descent_lemma

/-- Primal progress from smoothness. -/
theorem progress_lemma : ProgressLemma := Proof.progress_lemma

/-- `O(1/t)` convergence for open-loop steps, short steps and exact line search. -/
theorem standard_rate : StandardRate := Proof.standard_rate

/-- `O(1/t)` convergence in a Hilbert space, in the language of gradients. -/
theorem standard_rate_hilbert : StandardRateHilbert := Proof.standard_rate_hilbert

/-- The Farkas lemma for finitely generated cones. -/
theorem farkas_lemma : FarkasLemma := fun G _ hx => farkas G hx

/-- The minimal face of a point of a polytope: exposed, containing the point, and pushable. -/
theorem minimal_face : MinimalFace := fun _ _ hy =>
  ⟨minFace_exposed hy, mem_convexHull_minFace hy, fun _ hv => push_away hy hv⟩
-- DOCS_END_MAIN

end Lemmata.FrankWolfe
