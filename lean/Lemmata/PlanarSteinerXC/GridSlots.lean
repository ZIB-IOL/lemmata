module

public import Lemmata.PlanarSteinerXC.GridBasic

/-!
# Directions, slots and the planar cyclic order at a grid point

Around a grid point the four directions occur in the counterclockwise order `E, N, W, S`. The
gadget of the edge in direction `d` contributes two literal occurrences of the vertex variable,
in two consecutive *slots* `(d, false)`, `(d, true)`. The cyclic successor of a slot skips the
directions that are absent at the boundary. All facts about the sixteen presence patterns are
checked by evaluation in the kernel (`decide`).
-/

@[expose] public section

set_option autoImplicit false

namespace Lemmata.PlanarSteinerXC

namespace Grid

/-- The four directions, in counterclockwise order. -/
inductive Dir
  | E | N | W | S
  deriving DecidableEq, Repr

instance : Fintype Dir where
  elems := {.E, .N, .W, .S}
  complete := fun d => by cases d <;> simp

namespace Dir

/-- The next direction counterclockwise. -/
def succ : Dir → Dir
  | E => N | N => W | W => S | S => E

/-- The previous direction. -/
def pred : Dir → Dir
  | E => S | N => E | W => N | S => W

@[simp] theorem pred_succ (d : Dir) : pred (succ d) = d := by cases d <;> rfl
@[simp] theorem succ_pred (d : Dir) : succ (pred d) = d := by cases d <;> rfl

/-- The next direction present in a pattern (or `d` itself if none). -/
def nextIn (pat : Dir → Bool) (d : Dir) : Dir :=
  if pat (succ d) then succ d
  else if pat (succ (succ d)) then succ (succ d)
  else if pat (succ (succ (succ d))) then succ (succ (succ d))
  else d

/-- The previous direction present in a pattern. -/
def prevIn (pat : Dir → Bool) (d : Dir) : Dir :=
  if pat (pred d) then pred d
  else if pat (pred (pred d)) then pred (pred d)
  else if pat (pred (pred (pred d))) then pred (pred (pred d))
  else d

/-- Patterns arising at grid points: one of `E, W` and one of `N, S` is present. -/
def Good (pat : Dir → Bool) : Prop := (pat E = true ∨ pat W = true) ∧ (pat N = true ∨ pat S = true)

instance (pat : Dir → Bool) : Decidable (Good pat) := by unfold Good; infer_instance

/-- A pattern from four booleans. -/
def mk4 (a b c e : Bool) : Dir → Bool
  | E => a | N => b | W => c | S => e

theorem eq_mk4 (pat : Dir → Bool) : pat = mk4 (pat E) (pat N) (pat W) (pat S) := by
  funext d; cases d <;> rfl

theorem nextIn_present' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) →
    mk4 a b c e (nextIn (mk4 a b c e) d) = true := by decide

theorem prevIn_nextIn' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) → mk4 a b c e d = true →
    prevIn (mk4 a b c e) (nextIn (mk4 a b c e) d) = d := by decide

theorem nextIn_prevIn' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) → mk4 a b c e d = true →
    nextIn (mk4 a b c e) (prevIn (mk4 a b c e) d) = d := by decide

theorem prevIn_present' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) →
    mk4 a b c e (prevIn (mk4 a b c e) d) = true := by decide

theorem nextIn_ne' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) → mk4 a b c e d = true →
    nextIn (mk4 a b c e) d ≠ d := by decide

theorem nextIn_cyclic' : ∀ (a b c e : Bool) (d d' : Dir), Good (mk4 a b c e) →
    mk4 a b c e d = true → mk4 a b c e d' = true →
    (d' = d ∨ d' = nextIn (mk4 a b c e) d ∨ d' = nextIn (mk4 a b c e) (nextIn (mk4 a b c e) d) ∨
      d' = nextIn (mk4 a b c e) (nextIn (mk4 a b c e) (nextIn (mk4 a b c e) d))) := by decide

theorem nextIn_skip' : ∀ (a b c e : Bool) (d : Dir), Good (mk4 a b c e) → mk4 a b c e d = true →
    nextIn (mk4 a b c e) d = succ d ∨
      (mk4 a b c e (succ d) = false ∧ mk4 a b c e (pred (nextIn (mk4 a b c e) d)) = false) := by
  decide

theorem nextIn_present (pat : Dir → Bool) (d : Dir) (hg : Good pat) : pat (nextIn pat d) = true := by
  rw [eq_mk4 pat] at hg ⊢; exact nextIn_present' _ _ _ _ d hg

theorem prevIn_nextIn (pat : Dir → Bool) (d : Dir) (hg : Good pat) (hd : pat d = true) :
    prevIn pat (nextIn pat d) = d := by
  rw [eq_mk4 pat] at hg hd ⊢; exact prevIn_nextIn' _ _ _ _ d hg hd

theorem nextIn_prevIn (pat : Dir → Bool) (d : Dir) (hg : Good pat) (hd : pat d = true) :
    nextIn pat (prevIn pat d) = d := by
  rw [eq_mk4 pat] at hg hd ⊢; exact nextIn_prevIn' _ _ _ _ d hg hd

theorem prevIn_present (pat : Dir → Bool) (d : Dir) (hg : Good pat) : pat (prevIn pat d) = true := by
  rw [eq_mk4 pat] at hg ⊢; exact prevIn_present' _ _ _ _ d hg

theorem nextIn_ne (pat : Dir → Bool) (d : Dir) (hg : Good pat) (hd : pat d = true) :
    nextIn pat d ≠ d := by
  rw [eq_mk4 pat] at hg hd ⊢; exact nextIn_ne' _ _ _ _ d hg hd

theorem nextIn_cyclic (pat : Dir → Bool) (d d' : Dir) (hg : Good pat) (hd : pat d = true)
    (hd' : pat d' = true) :
    d' = d ∨ d' = nextIn pat d ∨ d' = nextIn pat (nextIn pat d) ∨
      d' = nextIn pat (nextIn pat (nextIn pat d)) := by
  rw [eq_mk4 pat] at hg hd hd' ⊢; exact nextIn_cyclic' _ _ _ _ d d' hg hd hd'

theorem nextIn_skip (pat : Dir → Bool) (d : Dir) (hg : Good pat) (hd : pat d = true) :
    nextIn pat d = succ d ∨ (pat (succ d) = false ∧ pat (pred (nextIn pat d)) = false) := by
  rw [eq_mk4 pat] at hg hd ⊢; exact nextIn_skip' _ _ _ _ d hg hd

end Dir

variable {h : ℕ}

/-- A direction is present at a point if the grid edge in that direction exists. -/
def present (p : Pt h) : Dir → Prop
  | .E => p.1.val + 1 < h
  | .N => p.2.val + 1 < h
  | .W => 0 < p.1.val
  | .S => 0 < p.2.val

instance (p : Pt h) (d : Dir) : Decidable (present p d) := by
  cases d <;> unfold present <;> infer_instance

/-- The presence pattern at a point. -/
def pat (p : Pt h) (d : Dir) : Bool := decide (present p d)

theorem pat_eq_true {p : Pt h} {d : Dir} : pat p d = true ↔ present p d := by simp [pat]

theorem pat_good (hh : 2 ≤ h) (p : Pt h) : Dir.Good (pat p) := by
  constructor
  · by_cases h1 : p.1.val + 1 < h
    · left; exact pat_eq_true.mpr h1
    · right; apply pat_eq_true.mpr; show 0 < p.1.val; lia
  · by_cases h1 : p.2.val + 1 < h
    · left; exact pat_eq_true.mpr h1
    · right; apply pat_eq_true.mpr; show 0 < p.2.val; lia

end Grid

end Lemmata.PlanarSteinerXC
