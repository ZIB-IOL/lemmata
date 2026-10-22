module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.LinearAdaptive
public import Lemmata.DistributionalLowerBounds.Core.Distributional.Scaling

@[expose] public section

/-!
# Same-threshold three-quarter probability bound

This proves the Markov conversion and finite-seed averaging, not just an
expectation theorem. The existing adaptive-process certificate is still an
explicit interface: constructing it from arbitrary numerical LMO transcripts
is not supplied here. The terminal deficit cap and loss comparison are also
explicit inputs; no project-local axioms or proof placeholders are used.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional
namespace FinitePMF

variable {Ω : Type*} [Fintype Ω]

noncomputable def prob (P : FinitePMF Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact P.expect (fun ω => if A ω then 1 else 0)

lemma prob_nonneg (P : FinitePMF Ω) (A : Ω → Prop) : 0 ≤ P.prob A := by
  classical
  exact P.expect_nonneg (fun ω => by split_ifs <;> norm_num)

lemma prob_compl (P : FinitePMF Ω) (A : Ω → Prop) :
    P.prob (fun ω => ¬ A ω) = 1 - P.prob A := by
  classical
  calc
    P.prob (fun ω => ¬ A ω) =
        P.expect (fun ω => 1 - if A ω then 1 else 0) := by
      unfold prob expect
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : A ω <;> simp [h]
    _ = 1 - P.prob A := by
      rw [P.expect_sub, P.expect_const]
      rfl

lemma prob_mono (P : FinitePMF Ω) (A B : Ω → Prop)
    (h : ∀ ω, A ω → B ω) : P.prob A ≤ P.prob B := by
  classical
  apply P.expect_mono
  intro ω
  by_cases ha : A ω
  · simp [ha, h ω ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> norm_num

/-- Markov's inequality in indicator form, retaining threshold equality. -/
lemma threshold_mul_prob_le_expect (P : FinitePMF Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) :
    a * P.prob (fun ω => a ≤ X ω) ≤ P.expect X := by
  classical
  rw [prob, ← P.expect_const_mul]
  apply P.expect_mono
  intro ω
  by_cases h : a ≤ X ω
  · simp [h]
  · simpa [h] using hX ω

/-- A deficit cap supplies the nonnegative variable required by Markov. -/
theorem prob_deficit_ge (P : FinitePMF Ω) (Delta : Ω → ℝ)
    (initial threshold budget : ℝ) (hgap : 0 < initial - threshold)
    (hcap : ∀ ω, Delta ω ≤ initial)
    (hdrop : initial - P.expect Delta ≤ budget) :
    1 - budget / (initial - threshold) ≤
      P.prob (fun ω => threshold ≤ Delta ω) := by
  classical
  let X := fun ω => initial - Delta ω
  have hX : ∀ ω, 0 ≤ X ω := fun ω => sub_nonneg.mpr (hcap ω)
  have hm := P.threshold_mul_prob_le_expect X hX (initial - threshold)
  have hsub := P.prob_mono (fun ω => ¬ threshold ≤ Delta ω)
      (fun ω => initial - threshold ≤ X ω) (by
        intro ω hω
        dsimp [X]
        linarith [lt_of_not_ge hω])
  have hmul := mul_le_mul_of_nonneg_left hsub hgap.le
  have he : P.expect X = initial - P.expect Delta := by
    dsimp [X]
    rw [P.expect_sub, P.expect_const]
  rw [he] at hm
  rw [P.prob_compl] at hmul
  have htotal : (initial - threshold) *
      (1 - P.prob (fun ω => threshold ≤ Delta ω)) ≤ budget :=
    (hmul.trans hm).trans hdrop
  have hdiv : 1 - P.prob (fun ω => threshold ≤ Delta ω) ≤
      budget / (initial - threshold) := (le_div_iff₀ hgap).2 (by nlinarith)
  linarith

/-- Independent product averaging of events. -/
lemma product_prob {S : Type*} [Fintype S]
    (P : FinitePMF S) (Q : FinitePMF Ω) (A : S → Ω → Prop) :
    (P.product Q).prob (fun pair => A pair.1 pair.2) =
      P.expect (fun seed => Q.prob (A seed)) := by
  classical
  unfold prob
  exact P.product_expect Q _

/-- A fixed finite instance attains at least the weighted mean. No realized
seed appears in the choice of this witness. -/
lemma exists_ge_of_le_expect (P : FinitePMF Ω) (X : Ω → ℝ) {a : ℝ}
    (hmean : a ≤ P.expect X) : ∃ ω, a ≤ X ω := by
  classical
  have hsupport : ∃ ω, 0 < P.weight ω := by
    by_contra! h
    have hz : ∀ ω, P.weight ω = 0 := fun ω => le_antisymm (h ω) (P.nonneg ω)
    have hs := P.sum_weight
    simp [hz] at hs
  by_contra! h
  obtain ⟨ω, hω⟩ := hsupport
  have hpos : 0 < P.expect (fun i => a-X i) := by
    apply Finset.sum_pos'
    · intro i _; exact mul_nonneg (P.nonneg i) (sub_pos.mpr (h i)).le
    · exact ⟨ω, Finset.mem_univ ω, mul_pos hω (sub_pos.mpr (h ω))⟩
  rw [P.expect_sub, P.expect_const] at hpos
  linarith

lemma product_expect_swap {S : Type*} [Fintype S]
    (P : FinitePMF S) (Q : FinitePMF Ω) (X : S × Ω → ℝ) :
    (P.product Q).expect X = Q.expect (fun ω => P.expect (fun s => X (s,ω))) := by
  rw [P.product_expect Q]
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem exists_instance_probability_ge {S : Type*} [Fintype S]
    (P : FinitePMF S) (Q : FinitePMF Ω) (A : S → Ω → Prop) {p : ℝ}
    (h : p ≤ (P.product Q).prob (fun pair => A pair.1 pair.2)) :
    ∃ ω, p ≤ P.prob (fun s => A s ω) := by
  classical
  have he : (P.product Q).prob (fun pair => A pair.1 pair.2) =
      Q.expect (fun ω => P.prob (fun s => A s ω)) := by
    unfold prob
    exact P.product_expect_swap Q _
  rw [he] at h
  exact Q.exists_ge_of_le_expect _ h

/-- Finite-probability stopping/failure conversion. The event containment must
be supplied by the actual truncation/padding construction. -/
theorem stopping_tail_of_event_cover (P : FinitePMF Ω) (Hard Long Fail : Ω → Prop)
    {p eta : ℝ} (hhard : p ≤ P.prob Hard) (hfail : P.prob Fail ≤ eta)
    (hcover : ∀ ω, Hard ω → Long ω ∨ Fail ω) : p-eta ≤ P.prob Long := by
  classical
  have hpoint : ∀ ω, (if Hard ω then (1 : ℝ) else 0) ≤
      (if Long ω then 1 else 0) + (if Fail ω then 1 else 0) := by
    intro ω
    by_cases hh : Hard ω
    · rcases hcover ω hh with h | h <;> simp [hh, h] <;> split_ifs <;> norm_num
    · simp only [hh, ↓reduceIte]; split_ifs <;> norm_num
  have h := P.expect_mono hpoint
  have he : P.expect (fun ω => (if Long ω then (1 : ℝ) else 0) +
      (if Fail ω then 1 else 0)) = P.prob Long + P.prob Fail := by
    unfold prob expect
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [he] at h
  change P.prob Hard ≤ P.prob Long + P.prob Fail at h
  linarith

end FinitePMF

/-- The pointwise arithmetic used on the large-deficit event. -/
theorem pointwise_loss_from_large_deficit {d rho C delta loss : ℝ}
    (hd : 0 < d) (hrho : 2 / d^2 ≤ rho) (hdelta : d^2/8 ≤ delta)
    (hloss : rho^2*C^2*delta^2/(48*d^2) ≤ loss) :
    C^2/(768*d^2) ≤ loss := by
  let P : FinitePMF Unit := ⟨fun _ => 1, fun _ => by norm_num, by simp⟩
  have h := loss_from_large_mean_deficit P (fun _ => delta) (fun _ => loss)
    hd hrho (by simpa using hdelta) (fun _ => hloss)
  simpa using h

/-- Exact horizon arithmetic for the same-threshold 3/4 bound, including T=0. -/
lemma linear_probability_budget (T : ℕ) :
    let d : ℝ := linearProofDimension T
    0 < initialDeficit (linearProofDimension T) - d^2/8 ∧
    6*(T : ℝ)*d ≤ (initialDeficit (linearProofDimension T) - d^2/8)/4 := by
  dsimp [initialDeficit]
  rw [linearProofDimension_cast]
  have ht : (0 : ℝ) ≤ T := by positivity
  constructor <;> nlinarith [sq_nonneg (T : ℝ)]

/-- Probability endpoint for the certified adaptive process. The cap, final
identity and loss comparison are explicit; none is inferred from an arbitrary
oracle merely because a certificate type has been declared. -/
theorem adaptive_probability_lower_bound_linear
    {Ω : Type*} [Fintype Ω] (P : FinitePMF Ω) (Delta loss : Ω → ℝ)
    (T : ℕ) (M : AdaptiveTranscriptProcess (linearProofDimension T) T)
    {rho : ℝ} (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : M.meanDeficit 0 = initialDeficit (linearProofDimension T))
    (hfinal : M.meanDeficit T = P.expect Delta)
    (hcap : ∀ ω, Delta ω ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ ω, rho^2*hardC (linearProofDimension T)^2*Delta ω^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤ loss ω) :
    (3 : ℝ)/4 ≤ P.prob (fun ω =>
      hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2) ≤ loss ω) := by
  have hd : (0 : ℝ) < linearProofDimension T := by
    exact_mod_cast (by have := linearProofDimension_ge_three T; omega : 0 < linearProofDimension T)
  have hbudget := linear_probability_budget T
  dsimp only at hbudget
  have ht := M.meanDeficit_telescope_linear
  rw [hzero, hfinal] at ht
  have hdrop : initialDeficit (linearProofDimension T) - P.expect Delta ≤
      6*(T : ℝ)*(linearProofDimension T : ℝ) := by linarith
  have hg := P.prob_deficit_ge Delta (initialDeficit (linearProofDimension T))
    ((linearProofDimension T : ℝ)^2/8) (6*(T : ℝ)*(linearProofDimension T : ℝ))
    hbudget.1 hcap hdrop
  have hquot : 6*(T : ℝ)*(linearProofDimension T : ℝ) /
      (initialDeficit (linearProofDimension T) - (linearProofDimension T : ℝ)^2/8)
      ≤ (1 : ℝ)/4 := (div_le_iff₀ hbudget.1).2 (by linarith [hbudget.2])
  have hgood : (3 : ℝ)/4 ≤ P.prob (fun ω => (linearProofDimension T : ℝ)^2/8 ≤ Delta ω) := by
    linarith
  apply hgood.trans
  apply P.prob_mono
  intro ω hω
  exact pointwise_loss_from_large_deficit hd
    (concrete_rho_lower_bound (linearProofDimension_ge_three T) hrhoIoo hrhoEq)
    hω (hloss ω)

/-- Average the probability theorem over an arbitrary finite independent seed. -/
theorem finiteSeed_strategy_probability_lower_bound_linear
    {Seed Ω Query Answer Output : Type} [Fintype Seed] [Fintype Ω]
    (seedLaw : FinitePMF Seed) (instanceLaw : FinitePMF Ω)
    (strategy : Seed → DeterministicAdaptiveStrategy Query Answer Output)
    (oracle : Ω → Query → Answer) (loss : Ω → Output → ℝ)
    (deficit : Seed → ℕ → Ω → ℝ) (T : ℕ)
    (certificate : ∀ seed, CertifiedStrategy (linearProofDimension T) T instanceLaw
      (strategy seed) oracle (deficit seed))
    {rho : ℝ} (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq : rhoLHS (hardWeight (linearProofDimension T))
      (hardTopWeight (linearProofDimension T)) rho = hardC (linearProofDimension T)^2)
    (hzero : ∀ seed, instanceLaw.expect (deficit seed 0) = initialDeficit (linearProofDimension T))
    (hcap : ∀ seed ω, deficit seed T ω ≤ initialDeficit (linearProofDimension T))
    (hloss : ∀ seed ω, rho^2*hardC (linearProofDimension T)^2*deficit seed T ω^2 /
      (48*(linearProofDimension T : ℝ)^2) ≤ loss ω ((strategy seed).run oracle ω T)) :
    (3 : ℝ)/4 ≤ (seedLaw.product instanceLaw).prob (fun pair =>
      hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2) ≤
        loss pair.2 ((strategy pair.1).run oracle pair.2 T)) := by
  rw [seedLaw.product_prob instanceLaw (fun seed ω =>
    hardC (linearProofDimension T)^2/(768*(linearProofDimension T : ℝ)^2) ≤
      loss ω ((strategy seed).run oracle ω T))]
  apply seedLaw.expect_ge_of_pointwise
  intro seed
  exact adaptive_probability_lower_bound_linear instanceLaw (deficit seed T)
    (fun ω => loss ω ((strategy seed).run oracle ω T)) T
    (certificate seed).toAdaptiveProcess hrhoIoo hrhoEq (hzero seed) rfl (hcap seed) (hloss seed)

end Lemmata.DistributionalLowerBounds.Core.Distributional
