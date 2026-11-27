module

public import Lemmata.FrankWolfePS.Upper.Main
public import Lemmata.FrankWolfePS.Model

@[expose] public section

/-!
# The matching upper bound as a method

The quadratic algorithm with a disclosed center, written as a `Method` requiring no more than
`n + 2` calls to a linear minimization oracle: one call in the direction `e` recovers a core
point, then `n + 1` Frank–Wolfe steps on the core, each asking the body oracle once (a zero
direction's reply is ignored). Against every exact oracle it returns the point of
`disclosedRun`, so the bounds of `disclosed_quadratic_upper` hold for it.
-/

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Frank–Wolfe on the core, forwards from iterate `x` at step `j`, for `m` more steps. -/
noncomputable def fwFrom (g core : E → E) : ℕ → E → ℕ → E
  | _, x, 0 => x
  | j, x, m + 1 => fwFrom g core (j + 1) (blend (fwStepSize j) x (core (g x))) m

theorem fwFrom_succ (g core : E → E) (j : ℕ) (x : E) (m : ℕ) :
    fwFrom g core j x (m + 1) =
      blend (fwStepSize (j + m)) (fwFrom g core j x m) (core (g (fwFrom g core j x m))) := by
  induction m generalizing j x with
  | zero => rfl
  | succ m ih =>
    rw [fwFrom, ih]
    simp only [fwFrom, Nat.add_assoc, Nat.add_comm 1 m]

theorem fwFrom_eq_fwRun (g core : E → E) (cost : E → ℕ) (x : E) (m : ℕ) :
    fwFrom g core 0 x m = (fwRun g core cost x m).1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [fwFrom_succ, ih, Nat.zero_add]; rfl

/-- The core Frank–Wolfe loop as a method: each step asks the body oracle in the direction
`g x` and converts the reply into a core point (`p` for the zero direction). -/
noncomputable def innerMethod (g : E → E) (p : E) (r : ℝ) (finish : E → E) :
    ℕ → E → (m : ℕ) → Method E m
  | _, x, 0 => .ret (finish x)
  | j, x, m + 1 => .ask (g x) fun y => innerMethod g p r finish (j + 1)
      (blend (fwStepSize j) x (if g x = 0 then p else y + r • unit (g x))) m

theorem innerMethod_run (g : E → E) (p : E) (r : ℝ) (finish : E → E) (O : E → E) (j : ℕ) (x : E)
    (m : ℕ) : (innerMethod g p r finish j x m).run O =
      finish (fwFrom g (fun q => if q = 0 then p else O q + r • unit q) j x m) := by
  induction m generalizing j x with
  | zero => rfl
  | succ m ih => simp only [innerMethod, Method.run, ih, fwFrom]

/-- **Frank–Wolfe on the inner parallel body.** For the known isotropic quadratic
`L ‖x - u‖² / 2`: one LMO call in the direction `e` gives a point of the inner parallel body,
then `n + 1` Frank–Wolfe steps with step sizes `2/(j + 2)` run on it, one LMO call each; the
output is `a + b` for the last iterate `a` and the point `b` of the ball closest to `u - a`. No
more than `n + 2` LMO calls, no gradient. -/
noncomputable def innerFrankWolfe (L r : ℝ) (u e : E) (n : ℕ) : Method E (n + 2) :=
  .ask e fun z => innerMethod (envGrad L r u) (z + r • unit e) r (liftInner r u) 0
    (z + r • unit e) (n + 1)

theorem innerFrankWolfe_run {C : Set E} (O : LMO C) {L : ℝ} (hL : 0 < L) (r : ℝ) (u e : E)
    (n : ℕ) : (innerFrankWolfe L r u e n).run O.query = (disclosedRun O u L r e (n + 1)).1 := by
  simp only [innerFrankWolfe, Method.run, innerMethod_run, disclosedRun, quadraticRun,
    recover_center hL, fwFrom_eq_fwRun _ _ realQueryCost]
  rfl

variable [ProperSpace E]

/-- **The matching upper bound, as a method.** On every compact convex body with `β`-Lipschitz
unit normals and every exact linear minimization oracle, the quadratic method (no more than
`n + 2` calls) returns a feasible point whose gap is at most `2L(diam C - 2/β)² / (n + 3)`. -/
theorem inner_frank_wolfe_upper {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C) {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (regular : LipschitzNormals C β) (hD : 2 * (1 / β) ≤ Metric.diam C)
    (O : LMO C) (u e : E) (he : e ≠ 0) (n : ℕ) :
    (innerFrankWolfe L (1 / β) u e n).run O.query ∈ C ∧
      ∀ w ∈ C, iso L u ((innerFrankWolfe L (1 / β) u e n).run O.query) - iso L u w ≤
        2 * L * (Metric.diam C - 2 * (1 / β)) ^ 2 / ((n : ℝ) + 3) := by
  rw [innerFrankWolfe_run O hL]
  obtain ⟨hm, -, -, hg⟩ := disclosed_quadratic_upper hc hv hβ hL regular hD O u e he n
  exact ⟨hm, hg⟩

end Lemmata.FrankWolfePS.Upper
