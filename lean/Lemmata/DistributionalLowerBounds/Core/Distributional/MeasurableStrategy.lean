module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.TerminalRegularity
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

/-!
# A small measurable oracle-controller model

The underlying strategy and its answer lists are unchanged. Measurability is
stated on finite products of answers, at precisely the horizon used. A vector
execution is proved equal to the existing list execution; measurability of the
actual output follows by recursion, not by assuming it. This file's generic
oracle-measurability hypothesis must be discharged for a concrete oracle.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

variable {Seed Query Answer Output Ω : Type}

/-- Finite-product version of exactly the same answer-list execution. -/
def vectorTranscript (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (ω : Ω) : (t : ℕ) → Seed → Fin t → Answer
  | 0, _ => Fin.elim0
  | t+1, seed =>
    let h := vectorTranscript strategy oracle ω t seed
    Fin.snoc h (oracle ω ((strategy seed).nextQuery t (List.ofFn h)))

lemma vectorTranscript_eq_list
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (ω : Ω) (seed : Seed) (t : ℕ) :
    List.ofFn (vectorTranscript strategy oracle ω t seed) =
      (strategy seed).transcript oracle ω t := by
  induction t with
  | zero => simp [vectorTranscript, DeterministicAdaptiveStrategy.transcript]
  | succ t ih =>
    simp only [vectorTranscript, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, ih, DeterministicAdaptiveStrategy.transcript_succ]

variable [MeasurableSpace Seed] [MeasurableSpace Query] [MeasurableSpace Answer]
    [MeasurableSpace Output]

/-- Original measurable-map assumptions, not a certificate of posterior or loss
properties. No intermediate feasibility, span restriction or finite seed space. -/
structure MeasurableStrategy
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output) (T : ℕ) : Prop where
  query : ∀ t < T, Measurable (fun z : Seed × (Fin t → Answer) =>
    (strategy z.1).nextQuery t (List.ofFn z.2))
  output : Measurable (fun z : Seed × (Fin T → Answer) =>
    (strategy z.1).output (List.ofFn z.2))

namespace MeasurableStrategy

variable {strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output}
    {T : ℕ} (hStrategy : MeasurableStrategy strategy T)
    (oracle : Ω → Query → Answer) (hOracle : ∀ ω, Measurable (oracle ω))

include hStrategy hOracle

lemma vectorTranscript_measurable (ω : Ω) (t : ℕ) (ht : t ≤ T) :
    Measurable (vectorTranscript strategy oracle ω t) := by
  induction t with
  | zero =>
    apply measurable_pi_iff.mpr
    intro i
    exact Fin.elim0 i
  | succ t ih =>
    have hp := ih (by omega)
    have hn := (hOracle ω).comp ((hStrategy.query t (by omega)).comp
      (measurable_id.prodMk hp))
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [vectorTranscript, Fin.snoc_last, Function.comp_def, id_eq] using hn
    · simpa only [vectorTranscript, Fin.snoc_castSucc] using
        (measurable_pi_iff.mp hp j)

/-- Measurability of the actual, previously defined `run`. -/
theorem run_measurable (ω : Ω) :
    Measurable (fun seed => (strategy seed).run oracle ω T) := by
  have h := hStrategy.output.comp (measurable_id.prodMk
    (hStrategy.vectorTranscript_measurable oracle hOracle ω T le_rfl))
  simpa only [Function.comp_def, id_eq, vectorTranscript_eq_list,
    DeterministicAdaptiveStrategy.run] using h

end MeasurableStrategy
end Lemmata.DistributionalLowerBounds.Core.Distributional
