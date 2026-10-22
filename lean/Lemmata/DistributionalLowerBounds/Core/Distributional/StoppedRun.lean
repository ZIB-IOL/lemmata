module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.StoppingController
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

/-!
# The output and number of calls of a stopping controller

The first stopping prefix is the actual output. On nontermination only, the
auxiliary total output is zero and the call count is infinity. The tail result
does not impose finite termination. Every halted output remains unrestricted.
-/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory
namespace DeterministicAdaptiveStrategy
variable {Q A O Ω : Type}

lemma firstStop_transcript_iff (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) {n T : ℕ} (hn : n ≤ T) :
    FirstStop r n (s.transcript oracle ω T) ↔ FirstStop r n (s.transcript oracle ω n) := by
  constructor
  · intro hr
    simpa only [s.transcript_take oracle ω hn] using hr.take (T := n) le_rfl
  · intro hr
    constructor
    · rw [s.transcript_take oracle ω hn]
      simpa only [List.take_of_length_le (by simp :
        (s.transcript oracle ω n).length ≤ n)] using hr.1
    · intro k hk
      rw [s.transcript_take oracle ω (by omega)]
      simpa only [s.transcript_take oracle ω (by omega : k ≤ n)] using hr.2 k hk

lemma firstStop_run_unique (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) {m n : ℕ}
    (hm : FirstStop r m (s.transcript oracle ω m))
    (hn : FirstStop r n (s.transcript oracle ω n)) : m = n :=
  firstStop_unique ((s.firstStop_transcript_iff r oracle ω (Nat.le_max_left m n)).mpr hm)
    ((s.firstStop_transcript_iff r oracle ω (Nat.le_max_right m n)).mpr hn)

lemma stoppedBy_run_iff (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) (T : ℕ) :
    StoppedBy r T (s.transcript oracle ω T) ↔
      ∃ n ≤ T, FirstStop r n (s.transcript oracle ω n) := by
  rw [stoppedBy_iff_firstStop]
  exact exists_congr (fun n => and_congr_right (fun hn => s.firstStop_transcript_iff r oracle ω hn))

noncomputable def callCount (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ n, FirstStop r n (s.transcript oracle ω n) then (Nat.find h : ℕ) else ⊤

lemma callCount_le_iff (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) (T : ℕ) :
    s.callCount r oracle ω ≤ (T : WithTop ℕ) ↔ StoppedBy r T (s.transcript oracle ω T) := by
  classical
  rw [s.stoppedBy_run_iff]
  by_cases h : ∃ n, FirstStop r n (s.transcript oracle ω n)
  · simp only [callCount, dif_pos h, Nat.cast_le]
    constructor
    · intro ht; exact ⟨Nat.find h, ht, Nat.find_spec h⟩
    · rintro ⟨n, hn, hr⟩; exact (Nat.find_min' h hr).trans hn
  · simp only [callCount, dif_neg h, WithTop.top_le_iff, WithTop.natCast_ne_top, false_iff]
    rintro ⟨n, _, hn⟩
    exact h ⟨n, hn⟩

variable {d : ℕ}

noncomputable def stoppedRun
    (s : DeterministicAdaptiveStrategy Q A (Fin d → ℝ))
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) : Fin d → ℝ := by
  classical
  exact ∑' n, if FirstStop r n (s.transcript oracle ω n) then s.run oracle ω n else 0

lemma stoppedRun_of_firstStop (s : DeterministicAdaptiveStrategy Q A (Fin d → ℝ))
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω) (n : ℕ)
    (hn : FirstStop r n (s.transcript oracle ω n)) :
    s.stoppedRun r oracle ω = s.run oracle ω n := by
  classical
  unfold stoppedRun
  rw [tsum_eq_single n]
  · simp [hn]
  · intro k hk
    have hnot : ¬ FirstStop r k (s.transcript oracle ω k) :=
      fun h => hk (s.firstStop_run_unique r oracle ω h hn)
    simp [hnot]

lemma stoppedRun_of_no_stop (s : DeterministicAdaptiveStrategy Q A (Fin d → ℝ))
    (r : StopRule A) (oracle : Ω → Q → A) (ω : Ω)
    (hn : ¬ ∃ n, FirstStop r n (s.transcript oracle ω n)) :
    s.stoppedRun r oracle ω = 0 := by
  classical
  have hnot (n : ℕ) : ¬ FirstStop r n (s.transcript oracle ω n) := fun h => hn ⟨n,h⟩
  simp [stoppedRun, hnot]

lemma padded_run_eq_stoppedRun (s : DeterministicAdaptiveStrategy Q A (Fin d → ℝ))
    (r : StopRule A) (idle : Q) (oracle : Ω → Q → A) (ω : Ω) (T : ℕ)
    (ht : StoppedBy r T (s.transcript oracle ω T)) :
    (s.padded r idle).run oracle ω T = s.stoppedRun r oracle ω := by
  obtain ⟨n, hn, hr⟩ := (s.stoppedBy_run_iff r oracle ω T).mp ht
  rw [s.stoppedRun_of_firstStop r oracle ω n hr]
  exact s.padded_run_of_firstStop r idle oracle ω hn
    ((s.firstStop_transcript_iff r oracle ω hn).mpr hr)

end DeterministicAdaptiveStrategy

section Measurability
variable {Seed Q A Ω : Type} [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A]
  {d T : ℕ}
  {s : Seed → DeterministicAdaptiveStrategy Q A (Fin d → ℝ)} {r : Seed → StopRule A}
  (oracle : Ω → Q → A) (hOracle : ∀ ω, Measurable (oracle ω))

include hOracle

lemma MeasurableStoppingStrategy.stoppedBy_run_set
    (hs : MeasurableStoppingStrategy s r T) (ω : Ω) :
    MeasurableSet {seed | StoppedBy (r seed) T ((s seed).transcript oracle ω T)} := by
  have hv := (hs.controller T le_rfl).vectorTranscript_measurable oracle hOracle ω T le_rfl
  simpa only [Set.preimage_ofPred_eq, vectorTranscript_eq_list, id_eq] using
    hs.stoppedBy_set.preimage (measurable_id.prodMk hv)

lemma MeasurableStoppingStrategy.firstStop_run_set
    (hs : MeasurableStoppingStrategy s r T) (ω : Ω) :
    MeasurableSet {seed | FirstStop (r seed) T ((s seed).transcript oracle ω T)} := by
  have hv := (hs.controller T le_rfl).vectorTranscript_measurable oracle hOracle ω T le_rfl
  simpa only [Set.preimage_ofPred_eq, vectorTranscript_eq_list, id_eq] using
    (hs.firstStop_set T le_rfl).preimage (measurable_id.prodMk hv)

lemma stoppedRun_measurable (hs : ∀ T, MeasurableStoppingStrategy s r T)
    (idle : Q) (ω : Ω) :
    Measurable (fun seed => (s seed).stoppedRun (r seed) oracle ω) := by
  classical
  apply measurable_of_tendsto_metrizable
    (f := fun n seed => ((s seed).padded (r seed) idle).run oracle ω n)
    (fun n => ((hs n).padded idle).run_measurable oracle hOracle ω)
  apply tendsto_pi_nhds.mpr
  intro seed
  apply Filter.Tendsto.congr' (h := tendsto_const_nhds)
  by_cases h : ∃ n, FirstStop (r seed) n ((s seed).transcript oracle ω n)
  · obtain ⟨n, hn⟩ := h
    apply Filter.eventually_atTop.mpr
    refine ⟨n, fun k hk => ?_⟩
    exact ((s seed).padded_run_eq_stoppedRun (r seed) idle oracle ω k
      (((s seed).stoppedBy_run_iff (r seed) oracle ω k).mpr ⟨n,hk,hn⟩)).symm
  · apply Filter.Eventually.of_forall
    intro n
    rw [(s seed).stoppedRun_of_no_stop (r seed) oracle ω h]
    symm
    apply (s seed).padded_run_of_not_stopped
    rw [(s seed).stoppedBy_run_iff]
    rintro ⟨k, _, hk⟩
    exact h ⟨k,hk⟩

end Measurability
end Lemmata.DistributionalLowerBounds.Core.Distributional
