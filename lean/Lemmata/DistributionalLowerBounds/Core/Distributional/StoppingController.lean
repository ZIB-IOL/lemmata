module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.ScaledController
public import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

/-!
# Actual stopping, zero-query padding and finite-horizon truncation

A stopping rule is a measurable Boolean function of the same answer prefix.
The original query/output maps are retained. The padded controller makes idle
queries after its first stop; truncation returns zero if no stop occurs by T.
No almost-sure feasibility, finite seed space or termination bound is imposed.
-/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory

abbrev StopRule (A : Type) := ℕ → List A → Bool

def FirstStop {A : Type} (r : StopRule A) (n : ℕ) (h : List A) : Prop :=
  r n (h.take n) = true ∧ ∀ k < n, r k (h.take k) = false

def StoppedBy {A : Type} (r : StopRule A) (T : ℕ) (h : List A) : Prop :=
  ∃ n ≤ T, r n (h.take n) = true

lemma firstStop_unique {A : Type} {r : StopRule A} {h : List A} {m n : ℕ}
    (hm : FirstStop r m h) (hn : FirstStop r n h) : m = n := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have := hn.2 m hlt; simp [hm.1] at this
  · exact heq
  · have := hm.2 n hgt; simp [hn.1] at this

lemma stoppedBy_iff_firstStop {A : Type} (r : StopRule A) (T : ℕ) (h : List A) :
    StoppedBy r T h ↔ ∃ n ≤ T, FirstStop r n h := by
  classical
  constructor
  · rintro ⟨n, hn, hr⟩
    have hex : ∃ k, r k (h.take k) = true := ⟨n, hr⟩
    refine ⟨Nat.find hex, (Nat.find_min' hex hr).trans hn, Nat.find_spec hex, ?_⟩
    intro k hk
    cases hh : r k (h.take k) with
    | false => rfl
    | true => exact False.elim (Nat.find_min hex hk hh)
  · rintro ⟨n, hn, hr⟩; exact ⟨n, hn, hr.1⟩

lemma FirstStop.take {A : Type} {r : StopRule A} {h : List A} {n T : ℕ}
    (hr : FirstStop r n h) (hn : n ≤ T) : FirstStop r n (h.take T) := by
  constructor
  · simpa only [List.take_take, min_eq_left hn] using hr.1
  · intro k hk
    simpa only [List.take_take, min_eq_left (by omega : k ≤ T)] using hr.2 k hk

namespace DeterministicAdaptiveStrategy

variable {Q A O Ω : Type}

lemma transcript_take (s : DeterministicAdaptiveStrategy Q A O)
    (oracle : Ω → Q → A) (ω : Ω) {m n : ℕ} (hm : m ≤ n) :
    (s.transcript oracle ω n).take m = s.transcript oracle ω m := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases hmn : m ≤ n
    · simp only [transcript_succ, List.take_append, transcript_length,
        Nat.sub_eq_zero_of_le hmn, List.take_zero, List.append_nil]
      exact ih hmn
    · have : m = n+1 := by omega
      subst m
      exact List.take_of_length_le (by simp)

variable [AddCommMonoid O]

noncomputable def truncatedOutput (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (h : List A) : O := by
  classical
  exact ∑ n ∈ Finset.range (h.length+1), if FirstStop r n h then s.output (h.take n) else 0

noncomputable def padded (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (idle : Q) : DeterministicAdaptiveStrategy Q A O := by
  classical
  exact { nextQuery := fun t h => if StoppedBy r t h then idle else s.nextQuery t h
          output := fun h => s.truncatedOutput r h }

lemma truncatedOutput_of_firstStop (s : DeterministicAdaptiveStrategy Q A O)
    {r : StopRule A} {h : List A} {n : ℕ} (hn : n ≤ h.length)
    (hr : FirstStop r n h) : s.truncatedOutput r h = s.output (h.take n) := by
  classical
  unfold truncatedOutput
  rw [Finset.sum_eq_single n]
  · simp [hr]
  · intro k hk hkn
    have hf : ¬ FirstStop r k h := fun hf => hkn (firstStop_unique hf hr)
    simp [hf]
  · simp [Finset.mem_range, hn]

lemma truncatedOutput_of_not_stopped (s : DeterministicAdaptiveStrategy Q A O)
    {r : StopRule A} {h : List A} (hr : ¬ StoppedBy r h.length h) :
    s.truncatedOutput r h = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro n hn
  have hf : ¬ FirstStop r n h := by
    intro hh
    exact hr ⟨n, Nat.le_of_lt_succ (Finset.mem_range.mp hn), hh.1⟩
  simp [hf]

/-- The actual padded run agrees with the original through its first stop. -/
lemma padded_transcript_before (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (idle : Q) (oracle : Ω → Q → A) (ω : Ω) (n : ℕ)
    (hn : ∀ k < n, r k (s.transcript oracle ω k) = false) :
    (s.padded r idle).transcript oracle ω n = s.transcript oracle ω n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun k hk => hn k (by omega))
    have hno : ¬ StoppedBy r n (s.transcript oracle ω n) := by
      rintro ⟨k, hk, hs⟩
      rw [s.transcript_take oracle ω hk, hn k (by omega)] at hs
      cases hs
    simp only [transcript_succ, he]
    change _ ++ [oracle ω (if StoppedBy r n (s.transcript oracle ω n)
      then idle else s.nextQuery n (s.transcript oracle ω n))] = _
    rw [if_neg hno]

lemma padded_run_of_firstStop (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (idle : Q) (oracle : Ω → Q → A) (ω : Ω) {n T : ℕ}
    (hn : n ≤ T) (hr : FirstStop r n (s.transcript oracle ω T)) :
    (s.padded r idle).run oracle ω T = s.run oracle ω n := by
  have hpre : ∀ k < n, r k (s.transcript oracle ω k) = false := by
    intro k hk
    simpa only [s.transcript_take oracle ω (by omega : k ≤ T)] using hr.2 k hk
  have he := s.padded_transcript_before r idle oracle ω n hpre
  have he' (k : ℕ) (hk : k ≤ n) :
      ((s.padded r idle).transcript oracle ω T).take k = s.transcript oracle ω k := by
    rw [(s.padded r idle).transcript_take oracle ω (by omega)]
    rw [← s.transcript_take oracle ω hk, ← he,
      (s.padded r idle).transcript_take oracle ω hk]
  have hf : FirstStop r n ((s.padded r idle).transcript oracle ω T) := by
    constructor
    · rw [he' n le_rfl]
      simpa only [s.transcript_take oracle ω hn] using hr.1
    · intro k hk
      rw [he' k (by omega)]
      exact hpre k hk
  change s.truncatedOutput r ((s.padded r idle).transcript oracle ω T) = _
  rw [s.truncatedOutput_of_firstStop (by simpa using hn) hf, he' n le_rfl]
  rfl

lemma padded_run_of_not_stopped (s : DeterministicAdaptiveStrategy Q A O)
    (r : StopRule A) (idle : Q) (oracle : Ω → Q → A) (ω : Ω) (T : ℕ)
    (hr : ¬ StoppedBy r T (s.transcript oracle ω T)) :
    (s.padded r idle).run oracle ω T = 0 := by
  have hpre : ∀ k < T, r k (s.transcript oracle ω k) = false := by
    intro k hk
    have hnot : r k (s.transcript oracle ω k) ≠ true := by
      intro h; apply hr; exact ⟨k, by omega, by rwa [s.transcript_take oracle ω (by omega)]⟩
    cases hh : r k (s.transcript oracle ω k) <;> simp_all
  have he := s.padded_transcript_before r idle oracle ω T hpre
  change s.truncatedOutput r ((s.padded r idle).transcript oracle ω T) = 0
  rw [he]
  apply s.truncatedOutput_of_not_stopped
  simpa only [transcript_length] using hr

end DeterministicAdaptiveStrategy

section Measurability
variable {Seed Q A O : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [MeasurableSpace A] [MeasurableSpace O]

/-- The original measurable query, stopping and output maps at all used depths. -/
structure MeasurableStoppingStrategy
    (s : Seed → DeterministicAdaptiveStrategy Q A O) (r : Seed → StopRule A) (T : ℕ) : Prop where
  controller : ∀ n ≤ T, MeasurableStrategy s n
  stop : ∀ n ≤ T, Measurable (fun z : Seed × (Fin n → A) => r z.1 n (List.ofFn z.2))

lemma measurable_prefix (T n : ℕ) (hn : n ≤ T) :
    Measurable (fun z : Seed × (Fin T → A) => (z.1, Fin.take n hn z.2)) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply (Fin.castLE hn i)).comp measurable_snd

variable {s : Seed → DeterministicAdaptiveStrategy Q A O} {r : Seed → StopRule A} {T : ℕ}

lemma MeasurableStoppingStrategy.rule_prefix (hs : MeasurableStoppingStrategy s r T)
    (n : ℕ) (hn : n ≤ T) :
    Measurable (fun z : Seed × (Fin T → A) => r z.1 n ((List.ofFn z.2).take n)) := by
  simpa only [Function.comp_def, Fin.ofFn_take_eq_take_ofFn] using
    (hs.stop n hn).comp (measurable_prefix T n hn)

lemma MeasurableStoppingStrategy.output_prefix (hs : MeasurableStoppingStrategy s r T)
    (n : ℕ) (hn : n ≤ T) :
    Measurable (fun z : Seed × (Fin T → A) => (s z.1).output ((List.ofFn z.2).take n)) := by
  simpa only [Function.comp_def, Fin.ofFn_take_eq_take_ofFn] using
    (hs.controller n hn).output.comp (measurable_prefix T n hn)

lemma MeasurableStoppingStrategy.firstStop_set (hs : MeasurableStoppingStrategy s r T)
    (n : ℕ) (hn : n ≤ T) :
    MeasurableSet {z : Seed × (Fin T → A) | FirstStop (r z.1) n (List.ofFn z.2)} := by
  have hf : MeasurableSet {z : Seed × (Fin T → A) |
      ∀ k, k < n → r z.1 k ((List.ofFn z.2).take k) = false} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : k < n
    · simpa only [hk, true_implies] using
        measurableSet_eq_fun (hs.rule_prefix k (by omega)) measurable_const
    · simp only [hk, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  exact (measurableSet_eq_fun (hs.rule_prefix n hn) measurable_const).inter hf

lemma MeasurableStoppingStrategy.stoppedBy_set (hs : MeasurableStoppingStrategy s r T) :
    MeasurableSet {z : Seed × (Fin T → A) | StoppedBy (r z.1) T (List.ofFn z.2)} := by
  change MeasurableSet {z : Seed × (Fin T → A) |
    ∃ n, n ≤ T ∧ r z.1 n ((List.ofFn z.2).take n) = true}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ≤ T
  · simpa only [hn, true_and] using
      measurableSet_eq_fun (hs.rule_prefix n hn) measurable_const
  · simp only [hn, false_and, Set.setOf_false]
    exact MeasurableSet.empty

lemma MeasurableStoppingStrategy.mono (hs : MeasurableStoppingStrategy s r T)
    {n : ℕ} (hn : n ≤ T) : MeasurableStoppingStrategy s r n :=
  ⟨fun k hk => hs.controller k (hk.trans hn), fun k hk => hs.stop k (hk.trans hn)⟩

lemma MeasurableStoppingStrategy.padded [AddCommMonoid O] [MeasurableAdd₂ O]
    (hs : MeasurableStoppingStrategy s r T) (idle : Q) :
    MeasurableStrategy (fun seed => (s seed).padded (r seed) idle) T := by
  classical
  constructor
  · intro t ht
    exact Measurable.ite ((hs.mono (by omega : t ≤ T)).stoppedBy_set)
      measurable_const ((hs.controller T le_rfl).query t ht)
  · change Measurable (fun z : Seed × (Fin T → A) =>
      ∑ n ∈ Finset.range ((List.ofFn z.2).length+1),
        if FirstStop (r z.1) n (List.ofFn z.2) then (s z.1).output ((List.ofFn z.2).take n) else 0)
    simp only [List.length_ofFn]
    apply Finset.measurable_sum
    intro n hn
    exact Measurable.ite (hs.firstStop_set n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
      (hs.output_prefix n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))) measurable_const

end Measurability
end Lemmata.DistributionalLowerBounds.Core.Distributional
