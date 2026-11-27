module

public import Lemmata.FrankWolfe.Polytope.Faces
public import Lemmata.FrankWolfe.Statement
public import Lemmata.FrankWolfe.Proof.Interfaces
public import Lemmata.FrankWolfe.Proof.Run

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
/-- The iterates of a Frank–Wolfe run on a convex set stay in it. -/
theorem fw_run_mem : FWRunMem := Proof.fw_run_mem

/-- The iterates `fwIterates` of an oracle form a Frank–Wolfe run. -/
theorem fwIterates_isFWRun : FWIteratesIsRun := Proof.fwIterates_isFWRun

/-- An `L`-smooth function is `L`-smooth over every set. -/
theorem smoothOn_of_smooth : SmoothOnOfSmooth := Proof.smoothOn_of_smooth

/-- Primal progress of a Frank–Wolfe run for a function that is smooth over the feasible set. -/
theorem run_progress : RunProgress := Proof.run_progress

/-- Scaling from a Hölderian error bound: `h^{1-θ} ‖x - y‖ ≤ μ f'(x)(x - y)` for a nearest
minimizer `y`. -/
theorem heb_scaling : HEBScaling := Proof.heb_scaling

/-- First-order strong convexity on a set. -/
theorem strongConvex_first_order : StrongConvexFirstOrder := Proof.strongConvex_first_order

/-- Strong convexity gives quadratic growth and a `(√(2/μ), 1/2)`-Hölderian error bound. -/
theorem strongConvex_heb : StrongConvexHEB := Proof.strongConvex_heb
-- DOCS_END_MAIN

end Lemmata.FrankWolfe
