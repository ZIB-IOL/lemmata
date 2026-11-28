module

public import Lemmata.OracleComplexity.Statement

@[expose] public section

/-!
# Scaled entropies

All entropies are kept multiplied by the probability of the event they condition on, so no division
occurs. `condEnt p G = ∑_{f ∈ G} -p_f log p_f + p(G) log p(G)` is `p(G)` times the entropy of the
instance given `G`; it splits along the answers to a query into the answer entropy and the parts of
the fibers (the chain rule). `scaledBin e P = P h(e/P)` is the binary entropy scaled by `P`; it is
superadditive, by concavity of `h`. Fano's inequality at a single output `o` reads
`condEnt p G ≤ scaledBin e p(G) + e log(|F| - 1)` with `e` the probability of the instances of `G`
other than `o`.
-/

namespace Lemmata.OracleComplexity

open Real

universe u

variable {F : Type u}

/-- `p(G)` times the entropy of the instance given `G`. -/
noncomputable def condEnt (p : F → ℝ) (G : Finset F) : ℝ :=
  ∑ f ∈ G, negMulLog (p f) - negMulLog (weight p G)

/-- The binary entropy scaled by `P`: `P h(e/P)` for `P > 0`. -/
noncomputable def scaledBin (e P : ℝ) : ℝ := negMulLog e + negMulLog (P - e) - negMulLog P

theorem weight_nonneg {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (G : Finset F) : 0 ≤ weight p G :=
  Finset.sum_nonneg fun f _ => hp f

/-- The entropy of `p` on `s` is at most the log of the size of `s`, in scaled form. -/
theorem sum_negMulLog_le {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (s : Finset F) :
    ∑ f ∈ s, negMulLog (p f) ≤ negMulLog (weight p s) + weight p s * Real.log s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [weight]
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => (s.card : ℝ)⁻¹) (p := p)
    (fun _ _ => inv_nonneg.mpr hn.le)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp) (fun f _ => Set.mem_Ici.mpr (hp f))
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have hinv : negMulLog ((s.card : ℝ)⁻¹) = (s.card : ℝ)⁻¹ * Real.log s.card := by
    rw [negMulLog, Real.log_inv]; ring
  rw [negMulLog_mul, hinv] at hJ
  unfold weight
  have h2 := mul_le_mul_of_nonneg_left hJ hn.le
  rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h2
  calc ∑ f ∈ s, negMulLog (p f) ≤ _ := h2
    _ = negMulLog (∑ f ∈ s, p f) + (∑ f ∈ s, p f) * Real.log s.card := by
        field_simp
        ring

open Classical in
/-- The chain rule: the entropy given `G` splits into the entropy of the answer and the entropies
given the fibers of the answer. -/
theorem condEnt_chain (p : F → ℝ) {Q A : Type u} (oracle : F → Q → A) (q : Q) (G : Finset F) :
    condEnt p G = answerEntropy p oracle q G +
      ∑ a ∈ G.image (fun f => oracle f q), condEnt p (G.filter (fun f => oracle f q = a)) := by
  unfold condEnt answerEntropy weight
  rw [Finset.sum_sub_distrib]
  have h1 := Finset.sum_fiberwise_of_maps_to (s := G) (t := G.image (fun f => oracle f q))
    (g := fun f => oracle f q) (fun f hf => Finset.mem_image_of_mem _ hf)
    (fun f => negMulLog (p f))
  rw [h1]
  ring

open Classical in
/-- Fano's inequality for a fixed output `o`, in scaled form. -/
theorem leaf_fano [Fintype F] {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (G : Finset F) (o : F) :
    condEnt p G ≤ scaledBin (weight p (G.filter (fun f => o ≠ f))) (weight p G) +
      weight p (G.filter (fun f => o ≠ f)) * Real.log ((Fintype.card F : ℝ) - 1) := by
  set G' := G.filter (fun f => o ≠ f) with hG'
  have hsplit : ∑ f ∈ G, negMulLog (p f) =
      ∑ f ∈ G', negMulLog (p f) + ∑ f ∈ G.filter (fun f => ¬ o ≠ f), negMulLog (p f) :=
    (Finset.sum_filter_add_sum_filter_not G _ _).symm
  have hw : weight p G = weight p G' + ∑ f ∈ G.filter (fun f => ¬ o ≠ f), p f :=
    (Finset.sum_filter_add_sum_filter_not G _ _).symm
  have hsing : G.filter (fun f => ¬ o ≠ f) = if o ∈ G then {o} else ∅ := by
    ext f
    simp only [Finset.mem_filter, not_not]
    split_ifs with h
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩; rfl
      · rintro rfl; exact ⟨h, rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro hf rfl
      exact h hf
  have hpart : ∑ f ∈ G.filter (fun f => ¬ o ≠ f), negMulLog (p f) =
      negMulLog (weight p G - weight p G') := by
    rw [hw, add_sub_cancel_left, hsing]
    split_ifs <;> simp
  have hcard : (G'.card : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by
    have hsub : G' ⊆ Finset.univ.erase o := fun f hf => by
      rw [hG', Finset.mem_filter] at hf
      exact Finset.mem_erase.mpr ⟨fun h => hf.2 h.symm, Finset.mem_univ f⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ] at h1
    have h2 : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨o⟩
    have : ((G'.card : ℕ) : ℝ) + 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast (by omega)
    linarith
  have hlog : weight p G' * Real.log G'.card ≤
      weight p G' * Real.log ((Fintype.card F : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos G'.card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero, mul_zero]
      have : G' = ∅ := Finset.card_eq_zero.mp h0
      rw [this]; simp [weight]
    · apply mul_le_mul_of_nonneg_left _ (weight_nonneg hp G')
      exact Real.log_le_log (by exact_mod_cast hpos) hcard
  have hJ := sum_negMulLog_le hp G'
  unfold condEnt scaledBin
  rw [hsplit, hpart]
  linarith

theorem scaledBin_eq {e P : ℝ} (hP : 0 < P) : scaledBin e P = P * binEntropy (e / P) := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold scaledBin
  have h1 : negMulLog e = e / P * negMulLog P + P * negMulLog (e / P) := by
    rw [← negMulLog_mul]; congr 1; field_simp
  have h2 : negMulLog (P - e) = (1 - e / P) * negMulLog P + P * negMulLog (1 - e / P) := by
    rw [← negMulLog_mul]; congr 1; field_simp
  rw [h1, h2]
  ring

/-- The scaled binary entropy is superadditive. -/
theorem scaledBin_super {e₁ P₁ e₂ P₂ : ℝ} (h₁ : 0 ≤ e₁) (h₁' : e₁ ≤ P₁) (h₂ : 0 ≤ e₂)
    (h₂' : e₂ ≤ P₂) :
    scaledBin e₁ P₁ + scaledBin e₂ P₂ ≤ scaledBin (e₁ + e₂) (P₁ + P₂) := by
  rcases eq_or_lt_of_le (h₁.trans h₁') with hP₁ | hP₁
  · have he : e₁ = 0 := by linarith
    subst he
    rw [← hP₁]
    simp [scaledBin]
  rcases eq_or_lt_of_le (h₂.trans h₂') with hP₂ | hP₂
  · have he : e₂ = 0 := by linarith
    subst he
    rw [← hP₂]
    simp [scaledBin]
  have hP : 0 < P₁ + P₂ := by linarith
  rw [scaledBin_eq hP₁, scaledBin_eq hP₂, scaledBin_eq hP]
  have hx : e₁ / P₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₁ hP₁.le, (div_le_one hP₁).mpr h₁'⟩
  have hy : e₂ / P₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₂ hP₂.le, (div_le_one hP₂).mpr h₂'⟩
  have hconc := strictConcave_binEntropy.concaveOn.2 hx hy
    (div_nonneg hP₁.le hP.le) (div_nonneg hP₂.le hP.le)
    (by rw [← add_div]; exact div_self hP.ne')
  have hpt : (P₁ / (P₁ + P₂)) • (e₁ / P₁) + (P₂ / (P₁ + P₂)) • (e₂ / P₂) =
      (e₁ + e₂) / (P₁ + P₂) := by
    simp only [smul_eq_mul]
    field_simp
  rw [hpt, smul_eq_mul, smul_eq_mul] at hconc
  have h3 := mul_le_mul_of_nonneg_left hconc hP.le
  calc P₁ * binEntropy (e₁ / P₁) + P₂ * binEntropy (e₂ / P₂) =
        (P₁ + P₂) * (P₁ / (P₁ + P₂) * binEntropy (e₁ / P₁) +
          P₂ / (P₁ + P₂) * binEntropy (e₂ / P₂)) := by
        field_simp
    _ ≤ _ := h3

theorem scaledBin_sum_le {ι : Type*} (s : Finset ι) (e P : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ e i)
    (h1 : ∀ i ∈ s, e i ≤ P i) :
    ∑ i ∈ s, scaledBin (e i) (P i) ≤ scaledBin (∑ i ∈ s, e i) (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scaledBin]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    have ih' := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    have := scaledBin_super (h0 i (Finset.mem_insert_self i s)) (h1 i (Finset.mem_insert_self i s))
      (Finset.sum_nonneg fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (Finset.sum_le_sum fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    linarith

end Lemmata.OracleComplexity
