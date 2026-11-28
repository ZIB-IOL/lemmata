module

public import Lemmata.OracleComplexity.Tree

@[expose] public section

/-!
# The string guessing problem

The strings that reach a query of an algorithm using the string guessing oracle form a cylinder:
the strings that agree with a partial assignment (or the empty set). On a cylinder of size `N`, the
answer to a query has entropy at most `2 log 2` (in scaled form, at most `2 N log 2`): a bit that is
already fixed either ends the answer or is skipped, and a free bit splits the cylinder into two
halves, the answer `0` on one half and a shifted answer on the other, at the cost of `N log 2` plus
the entropy on the half. With the uniform prior, Lemma III.1 then gives Proposition III.3.
-/

namespace Lemmata.OracleComplexity

open Real

variable {M : ℕ}

/-- The cylinder of a partial assignment `D`: the strings that agree with `D` where it is
defined. -/
def cyl (D : Fin M → Option Bool) : Finset (Fin M → Bool) :=
  Finset.univ.filter (fun S => ∀ i b, D i = some b → S i = b)

theorem mem_cyl {D : Fin M → Option Bool} {S : Fin M → Bool} :
    S ∈ cyl D ↔ ∀ i b, D i = some b → S i = b := by
  simp [cyl]

/-- The answer entropy of `g` on `G` for the uniform distribution, in counting form:
`∑_a -|G_a| log |G_a| + |G| log |G|`. -/
noncomputable def cAE {α : Type} [DecidableEq α] (G : Finset (Fin M → Bool))
    (g : (Fin M → Bool) → α) : ℝ :=
  ∑ a ∈ G.image g, negMulLog ((G.filter (fun S => g S = a)).card : ℝ) - negMulLog (G.card : ℝ)

theorem cAE_congr {α : Type} [DecidableEq α] {G : Finset (Fin M → Bool)}
    {g g' : (Fin M → Bool) → α} (h : ∀ S ∈ G, g S = g' S) : cAE G g = cAE G g' := by
  unfold cAE
  rw [Finset.image_congr (fun S hS => h S hS)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.filter_congr (fun S hS => by rw [h S hS])]

theorem cAE_const {α : Type} [DecidableEq α] {G : Finset (Fin M → Bool)}
    {g : (Fin M → Bool) → α} {a₀ : α} (h : ∀ S ∈ G, g S = a₀) : cAE G g = 0 := by
  unfold cAE
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp
  have himg : G.image g = {a₀} := by
    rw [Finset.image_congr (g := fun _ => a₀) (fun S hS => h S hS)]
    exact Finset.image_const hne a₀
  rw [himg, Finset.sum_singleton, Finset.filter_true_of_mem h, sub_self]

theorem cAE_comp {α β : Type} [DecidableEq α] [DecidableEq β] (G : Finset (Fin M → Bool))
    (g : (Fin M → Bool) → α) {φ : α → β} (hφ : Function.Injective φ) :
    cAE G (fun S => φ (g S)) = cAE G g := by
  unfold cAE
  have himg : G.image (fun S => φ (g S)) = (G.image g).image φ := by
    rw [Finset.image_image]; rfl
  rw [himg, Finset.sum_image (fun a _ b _ hab => hφ hab)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.filter_congr (fun S _ => hφ.eq_iff)]

theorem cAE_split {G G0 G1 : Finset (Fin M → Bool)} {g : (Fin M → Bool) → Option ℕ}
    (hG : G = G0 ∪ G1) (h0 : ∀ S ∈ G0, g S = some 0) (h1 : ∀ S ∈ G1, g S ≠ some 0)
    (hne : G0.Nonempty) :
    cAE G g = negMulLog (G0.card : ℝ) + negMulLog (G1.card : ℝ) - negMulLog (G.card : ℝ) +
      cAE G1 g := by
  unfold cAE
  have hnot : some 0 ∉ G1.image g := by
    rw [Finset.mem_image]
    rintro ⟨S, hS, hgS⟩
    exact h1 S hS hgS
  have himg : G.image g = insert (some 0) (G1.image g) := by
    rw [hG, Finset.image_union, Finset.image_congr (g := fun _ => some 0) (fun S hS => h0 S hS),
      Finset.image_const hne]
    exact (Finset.insert_eq _ _).symm
  rw [himg, Finset.sum_insert hnot]
  have hf0 : G.filter (fun S => g S = some 0) = G0 := by
    ext S
    rw [hG, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hS | hS, hgS⟩
      · exact hS
      · exact absurd hgS (h1 S hS)
    · intro hS
      exact ⟨Or.inl hS, h0 S hS⟩
  have hfa : ∀ a ∈ G1.image g, G.filter (fun S => g S = a) = G1.filter (fun S => g S = a) := by
    intro a ha
    have ha0 : a ≠ some 0 := fun e => hnot (e ▸ ha)
    ext S
    rw [hG, Finset.mem_filter, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hS | hS, hgS⟩
      · exact absurd (hgS.symm.trans (h0 S hS)) ha0
      · exact ⟨hS, hgS⟩
    · rintro ⟨hS, hgS⟩
      exact ⟨Or.inr hS, hgS⟩
  rw [hf0, Finset.sum_congr rfl (fun a ha => by rw [hfa a ha])]
  ring

theorem stringGuess_cons (S : Fin M → Bool) (i : Fin M) (b : Bool) (rest : List (Fin M × Bool)) :
    stringGuess S ((i, b) :: rest) =
      if S i = b then (stringGuess S rest).map (· + 1) else some 0 := by
  unfold stringGuess
  rw [List.findIdx?_cons]
  by_cases h : S i = b <;> simp [h]

theorem map_succ_ne_zero (x : Option ℕ) : x.map (· + 1) ≠ some 0 := by
  cases x <;> simp

theorem cyl_update_eq {D : Fin M → Option Bool} {i : Fin M} (hD : D i = none) (b : Bool) :
    (cyl D).filter (fun S => S i = b) = cyl (Function.update D i (some b)) := by
  ext S
  simp only [Finset.mem_filter, mem_cyl]
  constructor
  · rintro ⟨h, hb⟩ j c hj
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      cases hj
      exact hb
    · rw [Function.update_of_ne hji] at hj
      exact h j c hj
  · intro h
    refine ⟨fun j c hj => ?_, h i b (by rw [Function.update_self])⟩
    by_cases hji : j = i
    · subst hji
      rw [hD] at hj
      cases hj
    · exact h j c (by rw [Function.update_of_ne hji]; exact hj)

theorem cyl_flip_card {D : Fin M → Option Bool} {i : Fin M} (hD : D i = none) (b : Bool) :
    ((cyl D).filter (fun S => ¬ S i = b)).card = ((cyl D).filter (fun S => S i = b)).card := by
  have hflip : ∀ S ∈ cyl D, Function.update S i (!S i) ∈ cyl D := by
    intro S hS
    rw [mem_cyl] at hS ⊢
    intro j c hj
    by_cases hji : j = i
    · subst hji
      rw [hD] at hj
      cases hj
    · rw [Function.update_of_ne hji]
      exact hS j c hj
  have hinv : ∀ S : Fin M → Bool,
      Function.update (Function.update S i (!S i)) i (!(Function.update S i (!S i)) i) = S := by
    intro S
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  refine Finset.card_bij' (fun S _ => Function.update S i (!S i))
    (fun S _ => Function.update S i (!S i)) ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨hflip S hS.1, ?_⟩
    rw [Function.update_self]
    cases h : S i <;> cases b <;> simp_all
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨hflip S hS.1, ?_⟩
    rw [Function.update_self]
    cases h : S i <;> cases b <;> simp_all
  · intro S _
    exact hinv S
  · intro S _
    exact hinv S

theorem cyl_flip_nonempty {D : Fin M → Option Bool} {i : Fin M} (hD : D i = none) (b : Bool) :
    ((cyl D).filter (fun S => ¬ S i = b)).Nonempty := by
  refine ⟨Function.update (fun j => (D j).getD false) i (!b), ?_⟩
  rw [Finset.mem_filter, mem_cyl]
  refine ⟨fun j c hj => ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [hD] at hj
      cases hj
    · rw [Function.update_of_ne hji, hj]
      rfl
  · rw [Function.update_self]
    cases b <;> simp

/-- On a cylinder, the answer to a query has entropy at most `2 log 2`. -/
theorem cyl_bound : ∀ (q : List (Fin M × Bool)) (D : Fin M → Option Bool),
    cAE (cyl D) (fun S => stringGuess S q) ≤ 2 * Real.log 2 * (cyl D).card := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  intro q
  induction q with
  | nil =>
    intro D
    rw [cAE_const (g := fun S => stringGuess S []) (a₀ := none) (fun S _ => rfl)]
    positivity
  | cons g rest ih =>
    intro D
    obtain ⟨i, b⟩ := g
    cases hD : D i with
    | some c =>
      by_cases hcb : c = b
      · subst hcb
        have hsame : ∀ S ∈ cyl D, stringGuess S ((i, c) :: rest) =
            (fun S => Option.map (· + 1) (stringGuess S rest)) S := by
          intro S hS
          rw [stringGuess_cons, ite_eq_left (mem_cyl.mp hS i c hD)]
        rw [cAE_congr hsame, cAE_comp (cyl D) (fun S => stringGuess S rest)
          (Option.map_injective (add_left_injective 1))]
        exact ih D
      · have hzero : ∀ S ∈ cyl D, stringGuess S ((i, b) :: rest) = some 0 := by
          intro S hS
          rw [stringGuess_cons, ite_eq_right (by rw [mem_cyl.mp hS i c hD]; exact hcb)]
        rw [cAE_const hzero]
        positivity
    | none =>
      set G0 := (cyl D).filter (fun S => ¬ S i = b) with hG0
      set G1 := (cyl D).filter (fun S => S i = b) with hG1
      have hunion : cyl D = G0 ∪ G1 := by
        rw [Finset.union_comm]
        exact (Finset.filter_union_filter_not_eq _ _).symm
      have h0 : ∀ S ∈ G0, stringGuess S ((i, b) :: rest) = some 0 := by
        intro S hS
        rw [stringGuess_cons, ite_eq_right (Finset.mem_filter.mp hS).2]
      have h1 : ∀ S ∈ G1, stringGuess S ((i, b) :: rest) ≠ some 0 := by
        intro S hS
        rw [stringGuess_cons, ite_eq_left (Finset.mem_filter.mp hS).2]
        exact map_succ_ne_zero _
      rw [cAE_split hunion h0 h1 (cyl_flip_nonempty hD b)]
      have hG1eq : G1 = cyl (Function.update D i (some b)) := cyl_update_eq hD b
      have hrest : cAE G1 (fun S => stringGuess S ((i, b) :: rest)) ≤
          2 * Real.log 2 * G1.card := by
        have hsame : ∀ S ∈ G1, stringGuess S ((i, b) :: rest) =
            (fun S => Option.map (· + 1) (stringGuess S rest)) S := by
          intro S hS
          rw [stringGuess_cons, ite_eq_left (Finset.mem_filter.mp hS).2]
        rw [cAE_congr hsame, cAE_comp G1 (fun S => stringGuess S rest)
          (Option.map_injective (add_left_injective 1)), hG1eq]
        exact ih _
      have hc : G0.card = G1.card := cyl_flip_card hD b
      have htot : (cyl D).card = G1.card + G0.card := by
        rw [hG0, hG1, Finset.card_filter_add_card_filter_not]
      set n : ℕ := G1.card with hn
      have hnpos : 0 < n := by
        rw [← hc]
        exact Finset.card_pos.mpr (cyl_flip_nonempty hD b)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hent : negMulLog (n : ℝ) + negMulLog (n : ℝ) - negMulLog ((2 * n : ℕ) : ℝ) =
          2 * n * Real.log 2 := by
        push_cast
        unfold negMulLog
        rw [Real.log_mul (by norm_num) hnR.ne']
        ring
      rw [htot, hc, show n + n = 2 * n by ring]
      rw [hent]
      push_cast
      nlinarith [hrest]

/-- Sets of strings that are cylinders or empty. -/
def IsCyl (G : Finset (Fin M → Bool)) : Prop := (∃ D, G = cyl D) ∨ G = ∅

/-- The strings of a cylinder with a given answer form a cylinder or the empty set. -/
theorem cyl_filter_isCyl : ∀ (q : List (Fin M × Bool)) (D : Fin M → Option Bool)
    (a : Option ℕ), IsCyl ((cyl D).filter (fun S => stringGuess S q = a)) := by
  intro q
  induction q with
  | nil =>
    intro D a
    by_cases ha : a = none
    · subst ha
      left
      exact ⟨D, Finset.filter_true_of_mem (fun S _ => rfl)⟩
    · right
      exact Finset.filter_false_of_mem (fun S _ h => ha (h.symm.trans rfl))
  | cons g rest ih =>
    intro D a
    obtain ⟨i, b⟩ := g
    -- the shifted answers: `map succ (answer to rest) = a` is a condition on the answer to rest
    have hshift : ∀ (D' : Fin M → Option Bool), (∀ S ∈ cyl D', S i = b) → a ≠ some 0 →
        IsCyl ((cyl D').filter (fun S => stringGuess S ((i, b) :: rest) = a)) := by
      intro D' hb ha
      rcases a with _ | k
      · have e : (cyl D').filter (fun S => stringGuess S ((i, b) :: rest) = none) =
            (cyl D').filter (fun S => stringGuess S rest = none) := by
          apply Finset.filter_congr
          intro S hS
          rw [stringGuess_cons, ite_eq_left (hb S hS), Option.map_eq_none_iff]
        rw [e]
        exact ih D' none
      · rcases k with _ | k
        · exact absurd rfl ha
        · have e : (cyl D').filter (fun S => stringGuess S ((i, b) :: rest) = some (k + 1)) =
              (cyl D').filter (fun S => stringGuess S rest = some k) := by
            apply Finset.filter_congr
            intro S hS
            rw [stringGuess_cons, ite_eq_left (hb S hS)]
            constructor
            · intro h
              rcases hx : stringGuess S rest with _ | m
              · rw [hx] at h; simp at h
              · rw [hx] at h; simp at h; rw [h]
            · intro h
              rw [h]; rfl
          rw [e]
          exact ih D' (some k)
    cases hD : D i with
    | some c =>
      by_cases hcb : c = b
      · subst hcb
        by_cases ha : a = some 0
        · right
          apply Finset.filter_false_of_mem
          intro S hS
          rw [stringGuess_cons, ite_eq_left (mem_cyl.mp hS i c hD), ha]
          exact map_succ_ne_zero _
        · exact hshift D (fun S hS => mem_cyl.mp hS i c hD) ha
      · by_cases ha : a = some 0
        · left
          refine ⟨D, Finset.filter_true_of_mem (fun S hS => ?_)⟩
          rw [stringGuess_cons, ite_eq_right (by rw [mem_cyl.mp hS i c hD]; exact hcb), ha]
        · right
          apply Finset.filter_false_of_mem
          intro S hS h
          rw [stringGuess_cons, ite_eq_right (by rw [mem_cyl.mp hS i c hD]; exact hcb)] at h
          exact ha h.symm
    | none =>
      by_cases ha : a = some 0
      · left
        refine ⟨Function.update D i (some (!b)), ?_⟩
        rw [← cyl_update_eq hD (!b)]
        apply Finset.filter_congr
        intro S _
        rw [stringGuess_cons, ha]
        by_cases h : S i = b
        · rw [ite_eq_left h, h]
          constructor
          · intro h'; exact absurd h' (map_succ_ne_zero _)
          · intro h'; cases b <;> simp at h'
        · rw [ite_eq_right h]
          simp only [true_iff]
          cases h' : S i <;> cases b <;> simp_all
      · have e : (cyl D).filter (fun S => stringGuess S ((i, b) :: rest) = a) =
            (cyl (Function.update D i (some b))).filter
              (fun S => stringGuess S ((i, b) :: rest) = a) := by
          rw [← cyl_update_eq hD b, Finset.filter_filter]
          apply Finset.filter_congr
          intro S _
          constructor
          · intro h
            refine ⟨?_, h⟩
            by_contra hne
            rw [stringGuess_cons, ite_eq_right hne] at h
            exact ha h.symm
          · exact fun h => h.2
        rw [e]
        exact hshift _ (fun S hS => (mem_cyl.mp hS) i b (Function.update_self _ _ _)) ha

/-- The uniform answer entropy in terms of the counting form, for any decidability instance. -/
theorem answerEntropy_aux {α : Type} [hα : DecidableEq α] (c : ℝ) (G : Finset (Fin M → Bool))
    (g : (Fin M → Bool) → α) :
    ∑ a ∈ G.image g, negMulLog (∑ _f ∈ G.filter (fun f => g f = a), c) -
      negMulLog (∑ _f ∈ G, c) = c * cAE G g := by
  unfold cAE
  have h1 : ∀ s : Finset (Fin M → Bool), ∑ _f ∈ s, c = (s.card : ℝ) * c := fun s => by
    rw [Finset.sum_const, nsmul_eq_mul]
  simp only [h1, negMulLog_mul]
  have hcard : ∑ a ∈ G.image g, ((G.filter (fun f => g f = a)).card : ℝ) = G.card := by
    rw [Finset.card_eq_sum_card_image g G]
    push_cast
    rfl
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcard, mul_sub, Finset.mul_sum]
  ring

theorem answerEntropy_uniform (c : ℝ) (q : List (Fin M × Bool)) (G : Finset (Fin M → Bool)) :
    answerEntropy (fun _ => c) stringGuess q G = c * cAE G (fun S => stringGuess S q) := by
  have h := answerEntropy_aux (hα := fun a b => Classical.propDecidable (a = b)) c G
    (fun S => stringGuess S q)
  have hc : @cAE M (Option ℕ) (fun a b => Classical.propDecidable (a = b)) G
      (fun S => stringGuess S q) = cAE G (fun S => stringGuess S q) := by
    congr
  rw [← hc, ← h]
  rfl

/-- The string guessing oracle reveals at most `2 log 2` nats per query. -/
theorem string_info {X : Type} (t : QueryTree (List (Fin M × Bool)) (Option ℕ) X) :
    ∀ G, IsCyl G → InfoBounded (fun _ => ((2 : ℝ) ^ M)⁻¹) stringGuess (2 * Real.log 2) t G := by
  have hc : (0 : ℝ) ≤ ((2 : ℝ) ^ M)⁻¹ := by positivity
  induction t with
  | ret x => intro G _; simp only [InfoBounded]
  | ask q next ih =>
    intro G hG
    simp only [InfoBounded]
    refine ⟨?_, fun a => ih a _ ?_⟩
    · rcases hG with ⟨D, rfl⟩ | rfl
      · rw [answerEntropy_uniform]
        unfold weight
        rw [Finset.sum_const, nsmul_eq_mul]
        have := cyl_bound q D
        nlinarith
      · simp [answerEntropy, weight]
    · rcases hG with ⟨D, rfl⟩ | rfl
      · have := cyl_filter_isCyl q D a
        convert this using 2
      · right
        simp

namespace Proof

theorem string_guessing : StringGuessing := by
  intro M t Pe ET
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
  have h := info_lower_bound (fun _ => c) stringGuess (2 * Real.log 2) t (fun _ => hcpos.le) hsum
    hinfo
  have e1 : ∑ _f : Fin M → Bool, negMulLog c = M * Real.log 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardR, hc, negMulLog, Real.log_inv, Real.log_pow]
    field_simp
  have e2 : ∑ f : Fin M → Bool, c * (t.queries (stringGuess f) : ℝ) = ET := by
    rw [← Finset.mul_sum, hc]
    simp only [ET]
    rw [div_eq_inv_mul]
  have e3 : ∀ inst : DecidablePred (fun f : Fin M → Bool => t.output (stringGuess f) ≠ f),
      ∑ _f ∈ @Finset.filter _ _ inst Finset.univ, c = Pe := by
    intro inst
    rw [Finset.sum_const, nsmul_eq_mul, hc]
    simp only [Pe]
    rw [div_eq_mul_inv]
    congr
  rw [e1, e2, e3, hcardF] at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPe0 : 0 ≤ Pe := by positivity
  have hlogF : Real.log (((2 ^ M : ℕ) : ℝ) - 1) ≤ M * Real.log 2 := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      norm_num
    · have h1 : (1 : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) - 1 := by
        have : (2 : ℕ) ≤ 2 ^ M := Nat.le_self_pow (by omega) 2
        have : (2 : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      calc Real.log (((2 ^ M : ℕ) : ℝ) - 1) ≤ Real.log ((2 ^ M : ℕ) : ℝ) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = M * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hfano : Pe * Real.log (((2 ^ M : ℕ) : ℝ) - 1) ≤ Pe * (M * Real.log 2) :=
    mul_le_mul_of_nonneg_left hlogF hPe0
  have hmain : ((1 - Pe) * M - Real.binEntropy Pe / Real.log 2) * Real.log 2 ≤
      2 * ET * Real.log 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hlog2.ne']
    nlinarith
  have hmain' : (1 - Pe) * M - Real.binEntropy Pe / Real.log 2 ≤ 2 * ET :=
    le_of_mul_le_mul_right hmain hlog2
  have hbin : Real.binEntropy Pe / Real.log 2 ≤ 1 := by
    rw [div_le_one hlog2]
    exact Real.binEntropy_le_log_two
  constructor
  · linarith
  · linarith

end Proof

end Lemmata.OracleComplexity
