module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.StoppedRun

@[expose] public section

/-! A controller that reads previous query/answer pairs is simulated by the
unchanged answer-list controller. Reconstruction, stopping times, actual outputs,
and finite-product measurability are proved, not supplied as certificates. -/
namespace Lemmata.DistributionalLowerBounds.Core.Distributional
open MeasureTheory
namespace DeterministicAdaptiveStrategy
variable {Q A O Ω : Type}

def recoverHistory (s : DeterministicAdaptiveStrategy Q (Q × A) O) (h : List A) : List (Q × A) :=
  h.foldl (fun hist a => hist ++ [(s.nextQuery hist.length hist,a)]) []

@[simp] lemma recoverHistory_nil (s : DeterministicAdaptiveStrategy Q (Q × A) O) :
    s.recoverHistory [] = [] := rfl

lemma recoverHistory_snoc (s : DeterministicAdaptiveStrategy Q (Q × A) O) (h : List A) (a : A) :
    s.recoverHistory (h ++ [a]) = s.recoverHistory h ++
      [(s.nextQuery (s.recoverHistory h).length (s.recoverHistory h),a)] := by
  simp [recoverHistory, List.foldl_append]

@[simp] lemma recoverHistory_length (s : DeterministicAdaptiveStrategy Q (Q × A) O) (h : List A) :
    (s.recoverHistory h).length = h.length := by
  have he (h : List A) (start : List (Q × A)) :
      (h.foldl (fun hist a => hist ++ [(s.nextQuery hist.length hist,a)]) start).length =
        start.length+h.length := by
    induction h generalizing start with
    | nil => simp
    | cons a h ih => simp [List.foldl, ih, Nat.add_comm, Nat.add_left_comm]
  simpa [recoverHistory] using he h []

def feedback (s : DeterministicAdaptiveStrategy Q (Q × A) O) : DeterministicAdaptiveStrategy Q A O where
  nextQuery t h := s.nextQuery t (s.recoverHistory h)
  output h := s.output (s.recoverHistory h)

def recordedOracle (oracle : Ω → Q → A) (ω : Ω) (q : Q) : Q × A := (q,oracle ω q)

lemma feedback_transcript (s : DeterministicAdaptiveStrategy Q (Q × A) O)
    (oracle : Ω → Q → A) (ω : Ω) (t : ℕ) :
    s.recoverHistory (s.feedback.transcript oracle ω t) = s.transcript (recordedOracle oracle) ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [transcript_succ, transcript_succ, recoverHistory_snoc]
    simp only [recoverHistory_length, transcript_length]
    change s.recoverHistory (s.feedback.transcript oracle ω t) ++
      [(s.nextQuery t (s.recoverHistory (s.feedback.transcript oracle ω t)),
        oracle ω (s.nextQuery t (s.recoverHistory (s.feedback.transcript oracle ω t))))] = _
    rw [ih]
    rfl

lemma feedback_run (s : DeterministicAdaptiveStrategy Q (Q × A) O)
    (oracle : Ω → Q → A) (ω : Ω) (t : ℕ) :
    s.feedback.run oracle ω t = s.run (recordedOracle oracle) ω t := by
  change s.output (s.recoverHistory (s.feedback.transcript oracle ω t)) = _
  rw [feedback_transcript]
  rfl

def feedbackRule (s : DeterministicAdaptiveStrategy Q (Q × A) O) (r : StopRule (Q × A)) : StopRule A :=
  fun n h => r n (s.recoverHistory h)

lemma feedback_firstStop (s : DeterministicAdaptiveStrategy Q (Q × A) O)
    (r : StopRule (Q × A)) (oracle : Ω → Q → A) (ω : Ω) (t : ℕ) :
    FirstStop (s.feedbackRule r) t (s.feedback.transcript oracle ω t) ↔
      FirstStop r t (s.transcript (recordedOracle oracle) ω t) := by
  have he {k : ℕ} (hk : k ≤ t) :
      s.recoverHistory ((s.feedback.transcript oracle ω t).take k) =
        (s.transcript (recordedOracle oracle) ω t).take k := by
    rw [transcript_take _ _ _ hk, feedback_transcript, transcript_take _ _ _ hk]
  change (r t (s.recoverHistory ((s.feedback.transcript oracle ω t).take t)) = true ∧
    ∀ k < t, r k (s.recoverHistory ((s.feedback.transcript oracle ω t).take k)) = false) ↔ _
  simp only [he le_rfl, FirstStop]
  exact and_congr_right (fun _ => forall_congr' (fun k => forall_congr' (fun hk => by rw [he hk.le])))

lemma feedback_callCount (s : DeterministicAdaptiveStrategy Q (Q × A) O)
    (r : StopRule (Q × A)) (oracle : Ω → Q → A) (ω : Ω) :
    s.feedback.callCount (s.feedbackRule r) oracle ω = s.callCount r (recordedOracle oracle) ω := by
  classical
  have he : (∃ n, FirstStop (s.feedbackRule r) n (s.feedback.transcript oracle ω n)) ↔
      ∃ n, FirstStop r n (s.transcript (recordedOracle oracle) ω n) :=
    exists_congr (s.feedback_firstStop r oracle ω)
  by_cases hf : ∃ n, FirstStop (s.feedbackRule r) n (s.feedback.transcript oracle ω n)
  · have hg := he.mp hf
    simp only [callCount, dif_pos hf, dif_pos hg]
    exact congrArg (fun n : ℕ => (n : WithTop ℕ))
      (Nat.find_congr' (fun {n} => s.feedback_firstStop r oracle ω n))
  · have hg := mt he.mpr hf
    simp only [callCount, dif_neg hf, dif_neg hg]

lemma feedback_stoppedRun {d : ℕ} (s : DeterministicAdaptiveStrategy Q (Q × A) (Fin d → ℝ))
    (r : StopRule (Q × A)) (oracle : Ω → Q → A) (ω : Ω) :
    s.feedback.stoppedRun (s.feedbackRule r) oracle ω = s.stoppedRun r (recordedOracle oracle) ω := by
  unfold stoppedRun
  apply tsum_congr
  intro n
  rw [s.feedback_firstStop r oracle ω n, s.feedback_run oracle ω n]

def recoverVector (s : DeterministicAdaptiveStrategy Q (Q × A) O) :
    (t : ℕ) → (Fin t → A) → Fin t → Q × A
  | 0, _ => Fin.elim0
  | t+1, h =>
    let v := s.recoverVector t (fun i => h i.castSucc)
    Fin.snoc v (s.nextQuery t (List.ofFn v),h (Fin.last t))

lemma recoverVector_eq_list (s : DeterministicAdaptiveStrategy Q (Q × A) O)
    (t : ℕ) (h : Fin t → A) : List.ofFn (s.recoverVector t h) = s.recoverHistory (List.ofFn h) := by
  induction t with
  | zero => simp [recoverVector]
  | succ t ih =>
    rw [List.ofFn_succ' h, List.concat_eq_append, recoverHistory_snoc]
    simp only [recoverVector, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, ih, recoverHistory_length, List.length_ofFn]

end DeterministicAdaptiveStrategy

section Measurability
variable {Seed Q A O : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [MeasurableSpace A] [MeasurableSpace O]
  {s : Seed → DeterministicAdaptiveStrategy Q (Q × A) O} {T : ℕ}
open DeterministicAdaptiveStrategy

lemma MeasurableStrategy.recoverVector_measurable (hs : MeasurableStrategy s T)
    (t : ℕ) (ht : t ≤ T) :
    Measurable (fun z : Seed × (Fin t → A) => (s z.1).recoverVector t z.2) := by
  induction t with
  | zero => exact measurable_pi_iff.mpr (fun i => Fin.elim0 i)
  | succ t ih =>
    have hp := (ih (by omega)).comp (by fun_prop : Measurable
      (fun z : Seed × (Fin (t+1) → A) => (z.1,fun i : Fin t => z.2 i.castSucc)))
    have hq := (hs.query t (by omega)).comp (measurable_fst.prodMk hp)
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [recoverVector, Fin.snoc_last, Function.comp_def] using hq.prodMk
        (by fun_prop : Measurable (fun z : Seed × (Fin (t+1) → A) => z.2 (Fin.last t)))
    · simpa only [recoverVector, Fin.snoc_castSucc, Function.comp_def] using measurable_pi_iff.mp hp j

lemma MeasurableStrategy.feedback (hs : MeasurableStrategy s T) :
    MeasurableStrategy (fun seed => (s seed).feedback) T := by
  constructor
  · intro t ht
    have h := (hs.query t ht).comp (measurable_fst.prodMk (hs.recoverVector_measurable t ht.le))
    change Measurable (fun z : Seed × (Fin t → A) =>
      (s z.1).nextQuery t ((s z.1).recoverHistory (List.ofFn z.2)))
    simpa only [Function.comp_def, recoverVector_eq_list] using h
  · have h := hs.output.comp (measurable_fst.prodMk (hs.recoverVector_measurable T le_rfl))
    change Measurable (fun z : Seed × (Fin T → A) =>
      (s z.1).output ((s z.1).recoverHistory (List.ofFn z.2)))
    simpa only [Function.comp_def, recoverVector_eq_list] using h

lemma MeasurableStoppingStrategy.feedback {d : ℕ}
    {s : Seed → DeterministicAdaptiveStrategy Q (Q × A) (Fin d → ℝ)}
    {r : Seed → StopRule (Q × A)} (hs : MeasurableStoppingStrategy s r T) :
    MeasurableStoppingStrategy (fun seed => (s seed).feedback)
      (fun seed => (s seed).feedbackRule (r seed)) T := by
  constructor
  · intro n hn; exact (hs.controller n hn).feedback
  · intro n hn
    have h := (hs.stop n hn).comp (measurable_fst.prodMk
      ((hs.controller n hn).recoverVector_measurable n le_rfl))
    simpa only [Function.comp_def, recoverVector_eq_list, feedbackRule] using h

end Measurability
end Lemmata.DistributionalLowerBounds.Core.Distributional
