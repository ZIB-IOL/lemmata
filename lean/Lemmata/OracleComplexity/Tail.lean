module

public import Lemmata.OracleComplexity.StringGuess

@[expose] public section

/-!
# Lower bounds in probability (Lemma III.1 and Proposition III.3)

Running the chain rule of Lemma III.1 for `d` steps only gives
`H(F) ≤ C E[min(T, d)] + R_d`, where `R_d` is the entropy left at the leaves reached before depth
`d` and at the nodes of depth `d`. Fano's inequality bounds the former, the logarithm of the number
of instances the latter: `R_d ≤ h(E) + E log(|F| - 1) + P[T ≥ d] log|F|`, where `E ≤ P_e` is the
probability of an error before depth `d`. Rearranging bounds `P[T < d]`.
-/

namespace Lemmata.OracleComplexity

open Real

universe u

variable {F Q A X : Type u}

open Classical in
/-- The scaled entropy of the instance left after `d` queries: at the leaves reached before depth
`d` and at the nodes of depth `d`. -/
noncomputable def leafEntD (p : F → ℝ) (oracle : F → Q → A) :
    ℕ → QueryTree Q A X → Finset F → ℝ
  | 0, _, G => condEnt p G
  | _ + 1, .ret _, G => condEnt p G
  | d + 1, .ask q next, G => ∑ a ∈ G.image (fun f => oracle f q),
      leafEntD p oracle d (next a) (G.filter (fun f => oracle f q = a))

open Classical in
/-- The chain rule for `d` steps. -/
theorem info_bound_depth (p : F → ℝ) (oracle : F → Q → A) (C : ℝ) (d : ℕ) :
    ∀ (t : QueryTree Q A X) (G : Finset F), InfoBounded p oracle C t G →
      condEnt p G ≤ C * ∑ f ∈ G, p f * ((min (t.queries (oracle f)) d : ℕ) : ℝ) +
        leafEntD p oracle d t G := by
  induction d with
  | zero => intro t G _; simp [leafEntD]
  | succ d ih =>
    intro t G hG
    cases t with
    | ret x => simp [leafEntD, QueryTree.queries]
    | ask q next =>
      obtain ⟨hq, hnext⟩ := hG
      rw [condEnt_chain p oracle q G]
      have hsum : ∑ f ∈ G, p f *
          ((min ((QueryTree.ask q next).queries (oracle f)) (d + 1) : ℕ) : ℝ) =
          weight p G + ∑ a ∈ G.image (fun f => oracle f q),
            ∑ f ∈ G.filter (fun f => oracle f q = a),
              p f * ((min ((next a).queries (oracle f)) d : ℕ) : ℝ) := by
        simp only [QueryTree.queries, Nat.add_min_add_right, Nat.cast_add, Nat.cast_one, mul_add,
          mul_one, Finset.sum_add_distrib]
        rw [add_comm]
        unfold weight
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to (s := G) (t := G.image (fun f => oracle f q))
          (g := fun f => oracle f q) (fun f hf => Finset.mem_image_of_mem _ hf)]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun f hf => ?_
        rw [(Finset.mem_filter.mp hf).2]
      have h1 : ∑ a ∈ G.image (fun f => oracle f q),
          condEnt p (G.filter (fun f => oracle f q = a)) ≤
          ∑ a ∈ G.image (fun f => oracle f q),
            (C * ∑ f ∈ G.filter (fun f => oracle f q = a),
                p f * ((min ((next a).queries (oracle f)) d : ℕ) : ℝ) +
              leafEntD p oracle d (next a) (G.filter (fun f => oracle f q = a))) :=
        Finset.sum_le_sum fun a _ => ih (next a) _ (hnext a)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
      have hleaf : leafEntD p oracle (d + 1) (QueryTree.ask q next) G =
          ∑ a ∈ G.image (fun f => oracle f q),
            leafEntD p oracle d (next a) (G.filter (fun f => oracle f q = a)) := by
        simp only [leafEntD]
      rw [hsum, hleaf]
      nlinarith [hq, h1]

theorem condEnt_le_log [Fintype F] {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (G : Finset F) :
    condEnt p G ≤ weight p G * Real.log (Fintype.card F) := by
  have h := sum_negMulLog_le hp G
  unfold condEnt
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp [weight]
  have hlog : Real.log G.card ≤ Real.log (Fintype.card F) :=
    Real.log_le_log (by exact_mod_cast hG.card_pos) (by exact_mod_cast Finset.card_le_univ G)
  have := mul_le_mul_of_nonneg_left hlog (weight_nonneg hp G)
  linarith

open Classical in
/-- The entropy left after `d` queries: Fano's inequality at the leaves before depth `d`, and at
most `log|F|` per unit of probability at depth `d`. -/
theorem leafEntD_le [Fintype F] {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (oracle : F → Q → A) (d : ℕ) :
    ∀ (t : QueryTree Q A F) (G : Finset F),
      leafEntD p oracle d t G ≤
        scaledBin
            (weight p (G.filter (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f)))
            (weight p (G.filter (fun f => t.queries (oracle f) < d))) +
          weight p (G.filter (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f)) *
            Real.log ((Fintype.card F : ℝ) - 1) +
          (weight p G - weight p (G.filter (fun f => t.queries (oracle f) < d))) *
            Real.log (Fintype.card F) := by
  induction d with
  | zero =>
    intro t G
    have hf1 : G.filter (fun f => t.queries (oracle f) < 0 ∧ t.output (oracle f) ≠ f) = ∅ :=
      Finset.filter_false_of_mem (fun f _ h => Nat.not_lt_zero _ h.1)
    have hf2 : G.filter (fun f => t.queries (oracle f) < 0) = ∅ :=
      Finset.filter_false_of_mem (fun f _ h => Nat.not_lt_zero _ h)
    rw [hf1, hf2]
    simp only [leafEntD, weight, Finset.sum_empty, scaledBin, sub_zero, negMulLog_zero, add_zero,
      zero_mul, zero_add]
    have := condEnt_le_log hp G
    unfold weight at this
    exact this
  | succ d ih =>
    intro t G
    cases t with
    | ret x =>
      have hf1 : G.filter (fun f => (QueryTree.ret x : QueryTree Q A F).queries (oracle f) < d + 1 ∧
          (QueryTree.ret x : QueryTree Q A F).output (oracle f) ≠ f) = G.filter (fun f => x ≠ f) :=
        Finset.filter_congr (fun f _ => by simp [QueryTree.queries, QueryTree.output])
      have hf2 : G.filter (fun f => (QueryTree.ret x : QueryTree Q A F).queries (oracle f) <
          d + 1) = G :=
        Finset.filter_true_of_mem (fun f _ => by simp [QueryTree.queries])
      rw [hf1, hf2, sub_self, zero_mul, add_zero]
      exact leaf_fano hp G x
    | ask q next =>
      set img := G.image (fun f => oracle f q) with himg
      set Ga := fun a => G.filter (fun f => oracle f q = a) with hGa
      set E := fun a => weight p ((Ga a).filter
        (fun f => (next a).queries (oracle f) < d ∧ (next a).output (oracle f) ≠ f)) with hE
      set P := fun a => weight p ((Ga a).filter (fun f => (next a).queries (oracle f) < d))
        with hP
      have hleaf : leafEntD p oracle (d + 1) (QueryTree.ask q next) G =
          ∑ a ∈ img, leafEntD p oracle d (next a) (Ga a) := by
        simp only [leafEntD, himg, hGa]
      have h1 : ∑ a ∈ img, leafEntD p oracle d (next a) (Ga a) ≤
          ∑ a ∈ img, (scaledBin (E a) (P a) + E a * Real.log ((Fintype.card F : ℝ) - 1) +
            (weight p (Ga a) - P a) * Real.log (Fintype.card F)) :=
        Finset.sum_le_sum fun a _ => ih (next a) (Ga a)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        Finset.sum_sub_distrib] at h1
      have h2 := scaledBin_sum_le img E P (fun a _ => weight_nonneg hp _)
        (fun a _ => Finset.sum_le_sum_of_subset_of_nonneg
          (fun f hf => by
            simp only [Finset.mem_filter] at hf ⊢
            exact ⟨hf.1, hf.2.1⟩)
          (fun f _ _ => hp f))
      have hw : ∑ a ∈ img, weight p (Ga a) = weight p G := by
        unfold weight
        exact Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _
      have hEs : ∑ a ∈ img, E a = weight p (G.filter (fun f =>
          (QueryTree.ask q next).queries (oracle f) < d + 1 ∧
            (QueryTree.ask q next).output (oracle f) ≠ f)) := by
        simp only [hE, hGa, weight]
        rw [← Finset.sum_fiberwise_of_maps_to (t := img) (g := fun f => oracle f q)
          (fun f hf => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hf).1)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.filter_filter, Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro f _
        simp only [QueryTree.queries, QueryTree.output]
        constructor
        · rintro ⟨h1, h2, h3⟩
          subst h1
          exact ⟨⟨by omega, h3⟩, rfl⟩
        · rintro ⟨⟨h2, h3⟩, h1⟩
          subst h1
          exact ⟨rfl, by omega, h3⟩
      have hPs : ∑ a ∈ img, P a = weight p (G.filter (fun f =>
          (QueryTree.ask q next).queries (oracle f) < d + 1)) := by
        simp only [hP, hGa, weight]
        rw [← Finset.sum_fiberwise_of_maps_to (t := img) (g := fun f => oracle f q)
          (fun f hf => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hf).1)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.filter_filter, Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro f _
        simp only [QueryTree.queries]
        constructor
        · rintro ⟨h1, h2⟩
          subst h1
          exact ⟨by omega, rfl⟩
        · rintro ⟨h2, h1⟩
          subst h1
          exact ⟨rfl, by omega⟩
      rw [hleaf]
      rw [hw, hEs, hPs] at h1
      rw [hEs, hPs] at h2
      linarith

open Classical in
/-- The tail bound with the probability `E` of an error before depth `d`. -/
theorem info_tail [Fintype F] {p : F → ℝ} (oracle : F → Q → A) (C : ℝ) (t : QueryTree Q A F)
    (d : ℕ) (hp : ∀ f, 0 ≤ p f) (hsum : ∑ f, p f = 1) (hC : 0 ≤ C)
    (hinfo : InfoBounded p oracle C t Finset.univ) :
    (∑ f ∈ Finset.univ.filter (fun f => t.queries (oracle f) < d), p f) *
        Real.log (Fintype.card F) ≤
      Real.log (Fintype.card F) - ∑ f, negMulLog (p f) + C * d +
        binEntropy (∑ f ∈ Finset.univ.filter
          (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f), p f) +
        (∑ f ∈ Finset.univ.filter
          (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f), p f) *
          Real.log ((Fintype.card F : ℝ) - 1) := by
  have h1 := info_bound_depth p oracle C d t Finset.univ hinfo
  have h2 := leafEntD_le hp oracle d t Finset.univ
  have hw : weight p Finset.univ = 1 := hsum
  have hJ : condEnt p Finset.univ = ∑ f, negMulLog (p f) := by
    simp [condEnt, hw]
  rw [hJ] at h1
  rw [hw] at h2
  set P := weight p (Finset.univ.filter (fun f => t.queries (oracle f) < d)) with hPdef
  set E := weight p (Finset.univ.filter
    (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f)) with hEdef
  -- the expected truncated number of queries is at most `d`
  have hmin : C * ∑ f, p f * ((min (t.queries (oracle f)) d : ℕ) : ℝ) ≤ C * d := by
    apply mul_le_mul_of_nonneg_left _ hC
    calc ∑ f, p f * ((min (t.queries (oracle f)) d : ℕ) : ℝ) ≤ ∑ f, p f * (d : ℝ) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left
            (by exact_mod_cast min_le_right _ _) (hp f)
      _ = d := by rw [← Finset.sum_mul, hsum, one_mul]
  -- the scaled binary entropy is at most the binary entropy
  have hE0 : 0 ≤ E := weight_nonneg hp _
  have hEP : E ≤ P := Finset.sum_le_sum_of_subset_of_nonneg
    (fun f hf => by
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.1⟩) (fun f _ _ => hp f)
  have hP1 : P ≤ 1 := by
    rw [← hw]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun f _ _ => hp f)
  have hsb : scaledBin E P ≤ binEntropy E := by
    have := scaledBin_super hE0 hEP le_rfl (by linarith : (0 : ℝ) ≤ 1 - P)
    have h0 : scaledBin 0 (1 - P) = 0 := by simp [scaledBin]
    rw [h0, add_zero, add_zero, add_sub_cancel] at this
    have h1' : scaledBin E 1 = binEntropy E := by
      simp [scaledBin, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    linarith
  unfold weight at hPdef hEdef
  rw [← hPdef, ← hEdef]
  nlinarith

open Classical in
/-- The tail bound with `h(E) ≤ log 2` and `E ≤ P_e`. -/
theorem info_tail_simple [Fintype F] {p : F → ℝ} (oracle : F → Q → A) (C : ℝ)
    (t : QueryTree Q A F) (d : ℕ) (hp : ∀ f, 0 ≤ p f) (hsum : ∑ f, p f = 1) (hC : 0 ≤ C)
    (hinfo : InfoBounded p oracle C t Finset.univ)
    (hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) - 1)) :
    (∑ f ∈ Finset.univ.filter (fun f => t.queries (oracle f) < d), p f) *
        Real.log (Fintype.card F) ≤
      Real.log (Fintype.card F) - ∑ f, negMulLog (p f) + C * d + Real.log 2 +
        (∑ f ∈ Finset.univ.filter (fun f => t.output (oracle f) ≠ f), p f) *
          Real.log ((Fintype.card F : ℝ) - 1) := by
  have h := info_tail oracle C t d hp hsum hC hinfo
  have hEPe : ∑ f ∈ Finset.univ.filter
      (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f), p f ≤
      ∑ f ∈ Finset.univ.filter (fun f => t.output (oracle f) ≠ f), p f :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun f hf => by
        simp only [Finset.mem_filter] at hf ⊢
        exact ⟨hf.1, hf.2.2⟩) (fun f _ _ => hp f)
  have := mul_le_mul_of_nonneg_right hEPe hlog
  have hbin := binEntropy_le_log_two (p := ∑ f ∈ Finset.univ.filter
      (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f), p f)
  linarith

namespace Proof

open Classical in
theorem info_tail_bound : InfoTailBound.{u} := by
  intro F Q A _ p oracle C t d hp hsum hC hinfo hPe
  have h := info_tail oracle C t d hp hsum hC hinfo
  set Pe := ∑ f ∈ Finset.univ.filter (fun f => t.output (oracle f) ≠ f), p f with hPedef
  set E := ∑ f ∈ Finset.univ.filter
    (fun f => t.queries (oracle f) < d ∧ t.output (oracle f) ≠ f), p f with hEdef
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun f _ => hp f
  have hEPe : E ≤ Pe := Finset.sum_le_sum_of_subset_of_nonneg
    (fun f hf => by
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.2⟩) (fun f _ _ => hp f)
  have hbin : binEntropy E ≤ binEntropy Pe :=
    binEntropy_strictMonoOn.monotoneOn ⟨hE0, by linarith⟩ ⟨hE0.trans hEPe, by linarith⟩ hEPe
  -- `log(|F| - 1) ≥ 0`, as `|F| ≥ 1`
  have hcard : 1 ≤ Fintype.card F := by
    rcases Nat.eq_zero_or_pos (Fintype.card F) with h0 | h0
    · exfalso
      have : (Finset.univ : Finset F) = ∅ := Finset.univ_eq_empty_iff.mpr
        (Fintype.card_eq_zero_iff.mp h0)
      rw [this, Finset.sum_empty] at hsum
      exact zero_ne_one hsum
    · exact h0
  have hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) - 1) := by
    rcases eq_or_lt_of_le hcard with h1 | h1
    · rw [← h1]; simp
    · apply Real.log_nonneg
      have : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast h1
      linarith
  have := mul_le_mul_of_nonneg_right hEPe hlog
  linarith

open Classical in
theorem string_guessing_tail : StringGuessingTail := by
  intro M t d hM
  set c : ℝ := ((2 : ℝ) ^ M)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcardF : Fintype.card (Fin M → Bool) = 2 ^ M := by simp
  have hcardR : ((Finset.univ : Finset (Fin M → Bool)).card : ℝ) = 2 ^ M := by
    rw [Finset.card_univ, hcardF]
    push_cast
    rfl
  have hsum : ∑ _f : Fin M → Bool, c = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardR, hc]
    exact mul_inv_cancel₀ (by positivity)
  have hinfo : InfoBounded (fun _ => c) stringGuess (2 * Real.log 2) t Finset.univ :=
    string_info t Finset.univ (Or.inl ⟨fun _ => none, by ext S; simp [cyl]⟩)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogF : Real.log (((2 ^ M : ℕ) : ℝ) - 1) ≤ M * Real.log 2 := by
    have h1 : (1 : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ M := Nat.le_self_pow (by omega) 2
      have : (2 : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    calc Real.log (((2 ^ M : ℕ) : ℝ) - 1) ≤ Real.log ((2 ^ M : ℕ) : ℝ) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = M * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hlog0 : 0 ≤ Real.log ((Fintype.card (Fin M → Bool) : ℝ) - 1) := by
    rw [hcardF]
    apply Real.log_nonneg
    have : (2 : ℕ) ≤ 2 ^ M := Nat.le_self_pow (by omega) 2
    have : (2 : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h := info_tail_simple stringGuess (2 * Real.log 2) t d (fun _ => hcpos.le) hsum
    (by positivity) hinfo hlog0
  have e1 : ∑ _f : Fin M → Bool, negMulLog c = M * Real.log 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardR, hc, negMulLog, Real.log_inv, Real.log_pow]
    field_simp
  have e2 : Real.log (Fintype.card (Fin M → Bool)) = M * Real.log 2 := by
    rw [hcardF]; push_cast; rw [Real.log_pow]
  set Pe := ((Finset.univ.filter (fun S : Fin M → Bool =>
    t.output (stringGuess S) ≠ S)).card : ℝ) / 2 ^ M with hPedef
  have e3 : ∀ inst : DecidablePred (fun f : Fin M → Bool => t.output (stringGuess f) ≠ f),
      ∑ _f ∈ @Finset.filter _ _ inst Finset.univ, c = Pe := by
    intro inst
    rw [Finset.sum_const, nsmul_eq_mul, hc]
    simp only [Pe]
    rw [div_eq_mul_inv]
    congr
  set P := ∑ _f ∈ Finset.univ.filter (fun f : Fin M → Bool => t.queries (stringGuess f) < d), c
    with hPdef
  have hP : P = ((Finset.univ.filter (fun S : Fin M → Bool =>
      t.queries (stringGuess S) < d)).card : ℝ) / 2 ^ M := by
    rw [hPdef, Finset.sum_const, nsmul_eq_mul, hc, div_eq_mul_inv]
  rw [e1, e2, e3, hcardF] at h
  have hPe0 : 0 ≤ Pe := by positivity
  have hfano := mul_le_mul_of_nonneg_left hlogF hPe0
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h4 : P * (M * Real.log 2) ≤ 2 * Real.log 2 * d + Real.log 2 + Pe * (M * Real.log 2) := by
    linarith
  have key : P * M ≤ 2 * d + 1 + Pe * M := by
    have h3 : (P * M) * Real.log 2 ≤ (2 * d + 1 + Pe * M) * Real.log 2 :=
      calc (P * M) * Real.log 2 = P * (M * Real.log 2) := by ring
        _ ≤ 2 * Real.log 2 * d + Real.log 2 + Pe * (M * Real.log 2) := h4
        _ = (2 * d + 1 + Pe * M) * Real.log 2 := by ring
    exact le_of_mul_le_mul_right h3 hlog2
  rw [← hP]
  rw [← sub_le_iff_le_add', le_div_iff₀ hMpos, sub_mul]
  linarith

end Proof

end Lemmata.OracleComplexity
