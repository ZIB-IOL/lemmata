module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

@[expose] public section

/-!
# Methods that call a linear minimization oracle

A `Method E t` is an adaptive method requiring no more than `t` calls to a linear minimization
oracle on `E`: it either returns a point of `E` (feasible or not), or asks a direction `q` and
continues with the oracle's reply. Each continuation is an arbitrary function of the reply, so
every direction and the output may depend on all previous replies, and evaluations of a known
objective can be inlined. A randomized method is a family `s : Ω → Method E t` indexed by a
random tape `ω`, drawn from any probability law independently of the instance.

The same type describes the methods of the lower bounds (for every method ...) and of the
matching upper bound (there is a method ...).
-/

namespace Lemmata.FrankWolfePS

/-- An adaptive method requiring no more than `t` linear minimization oracle calls. -/
inductive Method (E : Type*) : ℕ → Type _
  | /-- Return a point. -/
    ret {t : ℕ} (x : E) : Method E t
  | /-- Ask the direction `q` and continue with the reply. -/
    ask {t : ℕ} (q : E) (next : E → Method E t) : Method E (t + 1)

/-- The point returned by a method when the oracle `O` answers every call. -/
def Method.run {E : Type*} {t : ℕ} : Method E t → (E → E) → E
  | .ret x, _ => x
  | .ask q next, O => (next (O q)).run O

/-- A randomized method is measurable if its output is a measurable function of the tape for
every measurable oracle. Methods given by jointly measurable query and output rules satisfy
this (`Unique.measurable_run`). -/
def Method.IsMeasurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {t : ℕ}
    (s : Ω → Method E t) : Prop :=
  ∀ O : E → E, Measurable O → Measurable fun ω => (s ω).run O

end Lemmata.FrankWolfePS
