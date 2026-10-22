module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.MeasurableStrategy

@[expose] public section

/-!
# Transport actual controllers through query/answer/output maps

This is a simulation of the unchanged list execution, not an assumption that
output laws agree. It is useful for scaling and coordinate conjugation.
-/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace DeterministicAdaptiveStrategy

variable {Q A O Q' A' O' Ω : Type}

def transport (s : DeterministicAdaptiveStrategy Q' A' O')
    (q : Q' → Q) (a : A → A') (o : O' → O) :
    DeterministicAdaptiveStrategy Q A O where
  nextQuery t h := q (s.nextQuery t (h.map a))
  output h := o (s.output (h.map a))

lemma transport_transcript (s : DeterministicAdaptiveStrategy Q' A' O')
    (q : Q' → Q) (a : A → A') (o : O' → O) (oracle : Ω → Q → A)
    (ω : Ω) (t : ℕ) :
    ((s.transport q a o).transcript oracle ω t).map a =
      s.transcript (fun ω p => a (oracle ω (q p))) ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [transport] at ih
    simp only [transcript_succ, transport, List.map_append, List.map_cons,
      List.map_nil, ih]

lemma transport_run (s : DeterministicAdaptiveStrategy Q' A' O')
    (q : Q' → Q) (a : A → A') (o : O' → O) (oracle : Ω → Q → A)
    (ω : Ω) (t : ℕ) :
    (s.transport q a o).run oracle ω t =
      o (s.run (fun ω p => a (oracle ω (q p))) ω t) := by
  change o (s.output (((s.transport q a o).transcript oracle ω t).map a)) = _
  rw [transport_transcript]
  rfl

lemma transcript_reindex {Ω' : Type} (s : DeterministicAdaptiveStrategy Q A O)
    (oracle : Ω' → Q → A) (f : Ω → Ω') (ω : Ω) (t : ℕ) :
    s.transcript (fun ω q => oracle (f ω) q) ω t = s.transcript oracle (f ω) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [transcript_succ, ih]

lemma run_reindex {Ω' : Type} (s : DeterministicAdaptiveStrategy Q A O)
    (oracle : Ω' → Q → A) (f : Ω → Ω') (ω : Ω) (t : ℕ) :
    s.run (fun ω q => oracle (f ω) q) ω t = s.run oracle (f ω) t := by
  simp only [run, transcript_reindex]

end DeterministicAdaptiveStrategy

lemma MeasurableStrategy.transport
    {Seed Q A O Q' A' O' : Type}
    [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace O]
    [MeasurableSpace Q'] [MeasurableSpace A'] [MeasurableSpace O']
    {s : Seed → DeterministicAdaptiveStrategy Q' A' O'} {T : ℕ}
    (hs : MeasurableStrategy s T)
    (q : Q' → Q) (a : A → A') (o : O' → O)
    (hq : Measurable q) (ha : Measurable a) (ho : Measurable o) :
    MeasurableStrategy (fun seed => (s seed).transport q a o) T := by
  have hm (t : ℕ) : Measurable (fun z : Seed × (Fin t → A) =>
      (z.1, fun i => a (z.2 i))) := by
    exact measurable_fst.prodMk (measurable_pi_iff.mpr (fun i =>
      ha.comp ((measurable_pi_apply i).comp measurable_snd)))
  constructor
  · intro t ht
    simpa only [DeterministicAdaptiveStrategy.transport, List.map_ofFn,
      Function.comp_def] using hq.comp ((hs.query t ht).comp (hm t))
  · simpa only [DeterministicAdaptiveStrategy.transport, List.map_ofFn,
      Function.comp_def] using ho.comp (hs.output.comp (hm T))

end Lemmata.DistributionalLowerBounds.Core.Distributional
