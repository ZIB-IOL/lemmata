module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringOrbit

structure Forest (n g : ℕ) where
  roots : List (Fin n)
  parent : Fin n → Fin n
  generator : Fin n → Fin g
  distance : Fin n → ℕ

def checkAt {n g : ℕ} (forest : Forest n g) (step : Fin g → Fin n → Fin n)
    (i : Fin n) : Bool :=
  decide (i ∈ forest.roots ∨
    (step (forest.generator i) i = forest.parent i ∧
     forest.distance (forest.parent i) < forest.distance i))

def check {n g : ℕ} (forest : Forest n g) (step : Fin g → Fin n → Fin n) : Bool :=
  (List.finRange n).all (checkAt forest step)

/-- Each checked edge transports the parameter to a strictly closer local representative. -/
theorem reach_root_of_checks {P : Type*} {n g : ℕ} (forest : Forest n g)
    (step : Fin g → Fin n → Fin n) (projection : P → Fin n)
    (move : Fin g → P → P) (allowed : P → Prop)
    (hlocal : ∀ a p, projection (move a p) = step a (projection p))
    (hallowed : ∀ a p, allowed p → allowed (move a p))
    (accepted : ∀ i, checkAt forest step i = true) :
    ∀ p, allowed p → ∃ q, allowed q ∧ projection q ∈ forest.roots := by
  have inductionStep : ∀ d p, forest.distance (projection p) = d → allowed p →
      ∃ q, allowed q ∧ projection q ∈ forest.roots := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro p hd hp
        have hedge := of_decide_eq_true (accepted (projection p))
        rcases hedge with hroot | ⟨hnext, hdist⟩
        · exact ⟨p, hp, hroot⟩
        · have hnew : projection (move (forest.generator (projection p)) p) =
              forest.parent (projection p) := (hlocal _ _).trans hnext
          have hlt : forest.distance (projection (move (forest.generator (projection p)) p)) < d := by
            rw [hnew, ← hd]
            exact hdist
          exact ih _ hlt _ rfl (hallowed _ _ hp)
  intro p hp
  exact inductionStep _ p rfl hp

theorem reach_root {P : Type*} {n g : ℕ} (forest : Forest n g)
    (step : Fin g → Fin n → Fin n) (projection : P → Fin n)
    (move : Fin g → P → P) (allowed : P → Prop)
    (hlocal : ∀ a p, projection (move a p) = step a (projection p))
    (hallowed : ∀ a p, allowed p → allowed (move a p))
    (accepted : check forest step = true) :
    ∀ p, allowed p → ∃ q, allowed q ∧ projection q ∈ forest.roots :=
  reach_root_of_checks forest step projection move allowed hlocal hallowed
    (fun i => List.all_eq_true.mp accepted i (List.mem_finRange _))

end Lemmata.CocubicCovering.CoveringOrbit
