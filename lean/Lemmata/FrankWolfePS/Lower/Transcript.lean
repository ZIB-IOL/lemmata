module

public import Lemmata.FrankWolfePS.Lower.Oracle
@[expose] public section

namespace Lemmata.FrankWolfePS
variable {ι O : Type*} [DecidableEq ι]

/-- The revealed labels of the membership experiment, in chronological order. -/
def Tree.trace {t} (s : Tree ι O t) (I : Finset ι) : List (ι × Bool) :=
  match s with
  | .leaf _ => []
  | .pass child => child.trace I
  | .probe i miss hit => if i ∈ I then (i, true)::hit.trace I else (i, false)::miss.trace I

def agrees (I : Finset ι) (l : List (ι × Bool)) : Prop :=
  ∀ e ∈ l, decide (e.1 ∈ I) = e.2

/-- Exact adaptive transcript fiber, including all negative observations. -/
theorem trace_fiber {t} (s : Tree ι O t) (I J : Finset ι) :
    s.trace J = s.trace I ↔ agrees J (s.trace I) := by
  induction s with
  | leaf => simp [Tree.trace, agrees]
  | pass _ ih => exact ih
  | probe i miss hit im iy =>
    by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;>
      simp [Tree.trace, agrees, hI, hJ, im, iy]

theorem uniform_trace_fiber {t} (s : Tree ι O t) (I : Finset ι) (prior : Finset (Finset ι)) :
    prior.filter (fun J => s.trace J = s.trace I) =
      prior.filter (fun J => ∀ e ∈ s.trace I, decide (e.1 ∈ J) = e.2) := by
  ext J
  simp only [Finset.mem_filter, trace_fiber, agrees]

end Lemmata.FrankWolfePS
