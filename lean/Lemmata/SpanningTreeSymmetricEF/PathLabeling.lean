module

public import Lemmata.SpanningTreeSymmetricEF.PathCertificate
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section

set_option backward.isDefEq.respectTransparency false


/-!
Uniform lifting of the ordered-placement certificate to actual bijections.
The denominator is the cardinality of the finite permutation fiber, not an
assumed factorial counting formula. No subgroup classification is used.
-/
namespace Lemmata.SpanningTreeSymmetricEF.PathLabeling
open scoped BigOperators
open PathCertificate
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered locations of the three distinguished labels. -/
def locations (s : Fin 3 ↪ V) (π : Equiv.Perm V) : V × V × V :=
  (π (s 0), π (s 1), π (s 2))

/-- All full bijective labelings extending the specified ordered locations. -/
def fiber (s : Fin 3 ↪ V) (t : V × V × V) : Finset (Equiv.Perm V) :=
  Finset.univ.filter (fun π => locations s π = t)

def tripleWeight (G : SimpleGraph V) [DecidableRel G.Adj] (t : V × V × V) : ℝ :=
  orderedWeight G t.1 t.2.1 t.2.2

/-- Actual signed weight of a full vertex permutation. -/
def weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (π : Equiv.Perm V) : ℝ :=
  tripleWeight G (locations s π) / (fiber s (locations s π)).card

private theorem fiber_nonempty (s : Fin 3 ↪ V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (fiber s (a,b,c)).Nonempty := by
  let f : Fin 3 → V := ![a,b,c]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair s f s.injective hf
  refine ⟨π, ?_⟩
  simp [fiber, locations, hπ, f]

/-- Unreachable location triples have zero weight, proved from injectivity
rather than postulated as a normalization interface. -/
theorem tripleWeight_eq_zero_of_fiber_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (t : V × V × V) (h : ¬ (fiber s t).Nonempty) :
    tripleWeight G t = 0 := by
  rcases t with ⟨a,b,c⟩
  have hn : ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
    rintro ⟨hab,hac,hbc⟩
    exact h (fiber_nonempty s a b c hab hac hbc)
  simp [tripleWeight, orderedWeight, hn]

/-- Exact finite-fiber integration formula for any observable of S locations.
This connects the full permutation measure to the earlier placement measure. -/
theorem sum_weight_locations (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (f : V × V × V → ℝ) :
    (∑ π, weight G s π * f (locations s π)) =
      ∑ a, ∑ b, ∑ c, orderedWeight G a b c * f (a,b,c) := by
  have hlocal (t : V × V × V) :
      (∑ π ∈ fiber s t, weight G s π * f (locations s π)) = tripleWeight G t * f t := by
    by_cases h : (fiber s t).Nonempty
    · have hc : ((fiber s t).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr h)
      calc
        _ = ∑ _π ∈ fiber s t, tripleWeight G t / (fiber s t).card * f t := by
          apply Finset.sum_congr rfl
          intro π hπ
          have he := (Finset.mem_filter.mp hπ).2
          simp [weight, he]
        _ = _ := by simp; field_simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp [tripleWeight_eq_zero_of_fiber_empty G s t h]
  have hsum : (∑ t : V × V × V, ∑ π ∈ fiber s t,
      weight G s π * f (locations s π)) = ∑ π, weight G s π * f (locations s π) := by
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [← hsum]
  simp_rw [hlocal]
  simp [Fintype.sum_prod_type, tripleWeight]

/-- Normalization on full permutations, including all complement labelings. -/
theorem weight_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) :
    ∑ π, weight G s π = 1 := by
  simpa using (sum_weight_locations G s (fun _ => 1)).trans
    (by simpa using orderedWeight_total G hd hn)

/-- Signed mass of an event on full label permutations. -/
def mass (G : SimpleGraph V) [DecidableRel G.Adj] (s : Fin 3 ↪ V)
    (P : Equiv.Perm V → Prop) [DecidablePred P] : ℝ :=
  ∑ π, if P π then weight G s π else 0

/-- Every occupied-position event is the actual pushforward of full labelings. -/
theorem mass_occupied (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (P : Finset V → Prop) [DecidablePred P] :
    mass G s (fun π => P {π (s 0), π (s 1), π (s 2)}) = eventMass G P := by
  classical
  simpa only [mass, eventMass, locations, mul_ite, mul_one, mul_zero] using
    sum_weight_locations G s (fun t => if P {t.1,t.2.1,t.2.2} then 1 else 0)

/-- A named distinguished label, not merely an occupied position. -/
theorem mass_first (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) (i : V) :
    mass G s (fun π => π (s 0) = i) = 1 / Fintype.card V := by
  classical
  have h := sum_weight_locations G s (fun t => if t.1 = i then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  simpa [mass, locations, mul_ite, Finset.sum_ite_irrel,
    orderedWeight_one G hd hn] using h

/-- Actual named SS fiber. -/
theorem mass_first_second (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V) (i j : V) :
    mass G s (fun π => π (s 0) = i ∧ π (s 1) = j) = edge G i j / (2 * Fintype.card V) := by
  classical
  have h := sum_weight_locations G s (fun t => if t.1 = i ∧ t.2.1 = j then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  simpa [mass, locations, mul_ite, ite_and, Finset.sum_ite_irrel,
    orderedWeight_pair G hd hn] using h

/-- Relabeling B does not alter the distinguished locations or their fiber. -/
theorem weight_mul_of_fixes (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (τ : Equiv.Perm V) (hτ : ∀ k, τ (s k) = s k)
    (π : Equiv.Perm V) : weight G s (π * τ) = weight G s π := by
  simp [weight, locations, Equiv.Perm.mul_apply, hτ]

/-- Change of variables for the actual permutation measure under B relabeling. -/
theorem mass_mul_of_fixes (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (τ : Equiv.Perm V) (hτ : ∀ k, τ (s k) = s k)
    (P : Equiv.Perm V → Prop) [DecidablePred P] :
    mass G s (fun π => P (π * τ)) = mass G s P := by
  have h := Equiv.sum_comp (Equiv.mulRight τ) (fun π => if P π then weight G s π else 0)
  simpa [mass, weight_mul_of_fixes G s τ hτ] using h

/-- Complement labels are actual vertices not among the three named S labels. -/
def background (s : Fin 3 ↪ V) : Finset V :=
  Finset.univ.filter (fun b => ∀ k, b ≠ s k)

@[simp] theorem mem_background (s : Fin 3 ↪ V) (b : V) :
    b ∈ background s ↔ ∀ k, b ≠ s k := by simp [background]

theorem swap_fixes (s : Fin 3 ↪ V) {b c : V}
    (hb : b ∈ background s) (hc : c ∈ background s) (k : Fin 3) :
    Equiv.swap b c (s k) = s k :=
  Equiv.swap_apply_of_ne_of_ne (Ne.symm ((mem_background s b).mp hb k))
    (Ne.symm ((mem_background s c).mp hc k))

/-- Uniform complement labels: every ordered distinct pair can be carried to
any other by a permutation fixing all S labels. -/
theorem exists_background_pair_map (s : Fin 3 ↪ V)
    (b c d e : ↥(background s)) (hbc : b ≠ c) (hde : d ≠ e) :
    ∃ τ : Equiv.Perm V, (∀ k, τ (s k) = s k) ∧ τ b = d ∧ τ c = e := by
  let f : Fin 2 → ↥(background s) := ![b,c]
  let g : Fin 2 → ↥(background s) := ![d,e]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨τ.subtypeCongr (Equiv.refl _), ?_, ?_, ?_⟩
  · intro k
    have hk : s k ∉ background s := by simp only [mem_background]; exact fun h => h k rfl
    simp [Equiv.Perm.subtypeCongr.right_apply _ _ hk]
  · simpa [f, g] using congrArg Subtype.val (hτ 0)
  · simpa [f, g] using congrArg Subtype.val (hτ 1)

/-- Ordered distinct background label pairs (a finite type, not a formula). -/
abbrev BackgroundPair (s : Fin 3 ↪ V) :=
  {p : ↥(background s) × ↥(background s) // p.1 ≠ p.2}

private theorem sum_injective_indicator {A D : Type*} [Fintype A] [DecidableEq D]
    (f : A → D) (hf : Function.Injective f) (d : D) (r : ℝ) :
    (∑ a, if f a = d then r else 0) = if d ∈ Set.range f then r else 0 := by
  classical
  by_cases h : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := h
    simp only [Set.mem_range_self, if_true, hf.eq_iff]
    simp
  · have hh (a : A) : f a ≠ d := fun ha => h ⟨a,ha⟩
    simp [h, hh]

@[simp] theorem background_preimage (s : Fin 3 ↪ V) (π : Equiv.Perm V) (i : V) :
    π.symm i ∈ background s ↔ i ∉ ({π (s 0), π (s 1), π (s 2)} : Finset V) := by
  simp [mem_background, Fin.forall_fin_succ, Equiv.symm_apply_eq]

private theorem background_pair_range (s : Fin 3 ↪ V) (π : Equiv.Perm V)
    (i j : V) (hij : i ≠ j) :
    (i,j) ∈ Set.range (fun p : BackgroundPair s => (π p.val.1, π p.val.2)) ↔
      i ∉ ({π (s 0), π (s 1), π (s 2)} : Finset V) ∧
      j ∉ ({π (s 0), π (s 1), π (s 2)} : Finset V) := by
  constructor
  · rintro ⟨⟨⟨b,c⟩,hbc⟩,h⟩
    have hi := congrArg Prod.fst h
    have hj := congrArg Prod.snd h
    dsimp at hi hj
    subst i; subst j
    simpa only [← background_preimage, Equiv.symm_apply_apply] using And.intro b.property c.property
  · rintro ⟨hi,hj⟩
    let b : ↥(background s) := ⟨π.symm i, (background_preimage s π i).mpr hi⟩
    let c : ↥(background s) := ⟨π.symm j, (background_preimage s π j).mpr hj⟩
    have hbc : b ≠ c := by
      intro h
      exact hij (π.symm.injective (congrArg Subtype.val h))
    exact ⟨⟨(b,c),hbc⟩, by simp [b,c]⟩

/-- Exchangeability of actual named BB fibers, derived by a change of variables. -/
theorem mass_background_pair_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (p q : BackgroundPair s) (i j : V) :
    mass G s (fun π => π p.val.1 = i ∧ π p.val.2 = j) =
      mass G s (fun π => π q.val.1 = i ∧ π q.val.2 = j) := by
  obtain ⟨τ,hτ,hb,hc⟩ := exists_background_pair_map s p.val.1 p.val.2 q.val.1 q.val.2
    p.property q.property
  have h := mass_mul_of_fixes G s τ hτ (fun π => π p.val.1 = i ∧ π p.val.2 = j)
  simpa [Equiv.Perm.mul_apply, hb, hc] using h.symm

/-- Summing actual named BB fibers recovers the complement occupation event. -/
theorem sum_mass_background_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (i j : V) (hij : i ≠ j) :
    (∑ p : BackgroundPair s, mass G s (fun π => π p.val.1 = i ∧ π p.val.2 = j)) =
      eventMass G (fun A => i ∉ A ∧ j ∉ A) := by
  rw [← mass_occupied G s]
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  let f : BackgroundPair s → V × V := fun p => (π p.val.1, π p.val.2)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact π.injective (congrArg Prod.fst h)
    · apply Subtype.ext
      exact π.injective (congrArg Prod.snd h)
  have h := sum_injective_indicator f hf (i,j) (weight G s π)
  simpa only [f, Prod.mk.injEq, background_pair_range s π i j hij] using h

/-- Exact named BB mass with a direct uniform finite denominator. -/
theorem mass_background_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (p : BackgroundPair s) (i j : V) (hij : i ≠ j) :
    mass G s (fun π => π p.val.1 = i ∧ π p.val.2 = j) =
      eventMass G (fun A => i ∉ A ∧ j ∉ A) / Fintype.card (BackgroundPair s) := by
  haveI : Nonempty (BackgroundPair s) := ⟨p⟩
  have hc : (Fintype.card (BackgroundPair s) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h := sum_mass_background_pair G s i j hij
  simp_rw [mass_background_pair_eq G s _ p i j] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  apply (eq_div_iff hc).mpr
  nlinarith [h]

/-- Nonnegative actual named BB fibers, not just color/occupation marginals. -/
theorem mass_background_pair_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (p : BackgroundPair s) (i j : V) :
    0 ≤ mass G s (fun π => π p.val.1 = i ∧ π p.val.2 = j) := by
  by_cases hij : i = j
  · subst j
    have hn (π : Equiv.Perm V) : ¬ (π p.val.1 = i ∧ π p.val.2 = i) := by
      rintro ⟨h₁,h₂⟩
      exact p.property (Subtype.ext (π.injective (h₁.trans h₂.symm)))
    simp [mass, hn]
  · rw [mass_background_pair G s p i j hij]
    exact div_nonneg (two_position_events_nonnegative G hd hn i j hij).2.2 (Nat.cast_nonneg _)

/-- All three named S-label marginals, not only their sum. -/
theorem mass_distinguished (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (k : Fin 3) (i : V) :
    mass G s (fun π => π (s k) = i) = 1 / Fintype.card V := by
  have h₂ : (∑ a, ∑ c, orderedWeight G a i c) = 1 / Fintype.card V := by
    simpa only [orderedWeight_swap_first G _ i] using orderedWeight_one G hd hn i
  have h₃ : (∑ a, ∑ b, orderedWeight G a b i) = 1 / Fintype.card V := by
    simpa only [orderedWeight_swap_last G _ _ i] using h₂
  fin_cases k
  · exact mass_first G s hd hn i
  · have h := sum_weight_locations G s (fun t => if t.2.1 = i then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    simpa [mass, locations, Finset.sum_ite_irrel, h₂] using h
  · have h := sum_weight_locations G s (fun t => if t.2.2 = i then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    simpa [mass, locations, Finset.sum_ite_irrel, h₃] using h

private theorem indicator_and (P Q : Prop) [Decidable P] [Decidable Q]
    (d : Decidable (P ∧ Q)) (r : ℝ) :
    @ite ℝ (P ∧ Q) d r 0 = if P then if Q then r else 0 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- All distinct named SS-label marginals. -/
theorem mass_distinguished_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (k l : Fin 3) (hkl : k ≠ l) (i j : V) :
    mass G s (fun π => π (s k) = i ∧ π (s l) = j) = edge G i j / (2 * Fintype.card V) := by
  have h₁ := orderedWeight_pair G hd hn i j
  have h₂ : (∑ b, orderedWeight G i b j) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_last G i _ j] using h₁
  have h₃ : (∑ c, orderedWeight G j i c) = edge G i j / (2 * Fintype.card V) := by
    simpa only [edge_symm G j i] using orderedWeight_pair G hd hn j i
  have h₄ : (∑ a, orderedWeight G a i j) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_first G _ i] using h₂
  have h₅ : (∑ b, orderedWeight G j b i) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_last G j _ i] using h₃
  have h₆ : (∑ a, orderedWeight G a j i) = edge G i j / (2 * Fintype.card V) := by
    simpa only [orderedWeight_swap_first G _ j] using h₅
  let loc (t : V × V × V) : Fin 3 → V := ![t.1,t.2.1,t.2.2]
  have h := sum_weight_locations G s (fun t => if loc t k = i ∧ loc t l = j then 1 else 0)
  have hl (π : Equiv.Perm V) (m : Fin 3) : loc (locations s π) m = π (s m) := by
    fin_cases m <;> rfl
  simp only [mul_ite, mul_one, mul_zero, hl] at h
  change mass G s (fun π => π (s k) = i ∧ π (s l) = j) = _ at h
  rw [h]
  fin_cases k <;> fin_cases l
  all_goals try exact (hkl rfl).elim
  all_goals simp only [loc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals simp [indicator_and, Finset.sum_ite_irrel, h₁, h₂, h₃, h₄, h₅, h₆]

/-- Mixed named-S/complement-position mass derived from the named SS moments. -/
theorem mass_distinguished_unoccupied (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (k : Fin 3) (i j : V) (hij : i ≠ j) :
    mass G s (fun π => π (s k) = i ∧ j ∉ ({π (s 0),π (s 1),π (s 2)} : Finset V)) =
      (1 - edge G i j) / Fintype.card V := by
  have hsplit : mass G s (fun π => π (s k) = i ∧
      j ∉ ({π (s 0),π (s 1),π (s 2)} : Finset V)) =
      mass G s (fun π => π (s k) = i) -
        ∑ l : Fin 3, mass G s (fun π => π (s k) = i ∧ π (s l) = j) := by
    unfold mass
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro π _
    have hinj : Function.Injective (fun l => π (s l)) := π.injective.comp s.injective
    have he := sum_injective_indicator (fun l => π (s l)) hinj j (weight G s π)
    have hr : j ∈ Set.range (fun l => π (s l)) ↔
        j ∈ ({π (s 0),π (s 1),π (s 2)} : Finset V) := by
      simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
    by_cases hk : π (s k) = i
    · simp only [hk, true_and, if_true]
      rw [he]
      simp only [hr]
      split_ifs <;> ring
    · simp [hk]
  rw [hsplit, mass_distinguished G s hd hn]
  have hm (l : Fin 3) : mass G s (fun π => π (s k) = i ∧ π (s l) = j) =
      if l = k then 0 else edge G i j / (2 * Fintype.card V) := by
    split_ifs with h
    · subst l
      have hh (π : Equiv.Perm V) : ¬ (π (s k) = i ∧ π (s k) = j) := by
        rintro ⟨hi,hj⟩; exact hij (hi.symm.trans hj)
      simp [mass, hh]
    · exact mass_distinguished_pair G s hd hn k l (Ne.symm h) i j
  simp_rw [hm]
  fin_cases k <;> simp [Fin.sum_univ_succ] <;> ring

/-- Exchangeability of a named B label while a named S label is fixed. -/
theorem mass_mixed_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (k : Fin 3) (b c : ↥(background s)) (i j : V) :
    mass G s (fun π => π (s k) = i ∧ π b = j) =
      mass G s (fun π => π (s k) = i ∧ π c = j) := by
  have h := mass_mul_of_fixes G s (Equiv.swap (b : V) c)
    (swap_fixes s b.property c.property) (fun π => π (s k) = i ∧ π b = j)
  simpa [Equiv.Perm.mul_apply, swap_fixes s b.property c.property] using h.symm

/-- Summing named SB events is the actual mixed position event. -/
theorem sum_mass_mixed (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (k : Fin 3) (i j : V) :
    (∑ b : ↥(background s), mass G s (fun π => π (s k) = i ∧ π b = j)) =
      mass G s (fun π => π (s k) = i ∧ j ∉ ({π (s 0),π (s 1),π (s 2)} : Finset V)) := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  have hf : Function.Injective (fun b : ↥(background s) => π b) :=
    π.injective.comp Subtype.val_injective
  have hr : j ∈ Set.range (fun b : ↥(background s) => π b) ↔ π.symm j ∈ background s := by
    constructor
    · rintro ⟨b,rfl⟩; simp
    · intro h; exact ⟨⟨π.symm j,h⟩, π.apply_symm_apply j⟩
  by_cases hk : π (s k) = i
  · simp only [hk, true_and]
    simpa only [hr, background_preimage] using
      sum_injective_indicator (fun b : ↥(background s) => π b) hf j (weight G s π)
  · simp [hk]

/-- Exact actual named SB fiber with direct uniform complement denominator. -/
theorem mass_mixed (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (k : Fin 3) (b : ↥(background s)) (i j : V) (hij : i ≠ j) :
    mass G s (fun π => π (s k) = i ∧ π b = j) =
      ((1 - edge G i j) / Fintype.card V) / (background s).card := by
  have hc : ((background s).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨(b : V), b.property⟩ : (background s).card ≠ 0)
  have h := sum_mass_mixed G s k i j
  simp_rw [mass_mixed_eq G s k _ b i j] at h
  rw [mass_distinguished_unoccupied G s hd hn k i j hij] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at h
  apply (eq_div_iff hc).mpr
  nlinarith [h]

/-- Actual named SB fibers are nonnegative, including impossible repeated positions. -/
theorem mass_mixed_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (k : Fin 3) (b : ↥(background s)) (i j : V) :
    0 ≤ mass G s (fun π => π (s k) = i ∧ π b = j) := by
  by_cases hij : i = j
  · subst j
    have hh (π : Equiv.Perm V) : ¬ (π (s k) = i ∧ π b = i) := by
      rintro ⟨hi,hb⟩
      exact (mem_background s b).mp b.property k (π.injective (hb.trans hi.symm))
    simp [mass, hh]
  · rw [mass_mixed G s hd hn k b i j hij]
    have he : 0 ≤ 1 - edge G i j := by unfold edge; split_ifs <;> norm_num
    exact div_nonneg (div_nonneg he (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- A single arbitrary named label has nonnegative mass. -/
theorem mass_label_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (a i : V) : 0 ≤ mass G s (fun π => π a = i) := by
  by_cases ha : ∃ k, a = s k
  · obtain ⟨k,rfl⟩ := ha
    rw [mass_distinguished G s hd hn]
    positivity
  · have hb : a ∈ background s := by simpa only [mem_background, not_exists] using ha
    have hsum : (∑ j, mass G s (fun π => π (s 0) = j ∧ π a = i)) =
        mass G s (fun π => π a = i) := by
      unfold mass
      rw [Finset.sum_comm]
      simp [ite_and, Finset.sum_ite_eq]
    rw [← hsum]
    exact Finset.sum_nonneg (fun j _ => mass_mixed_nonneg G s hd hn 0 ⟨a,hb⟩ j i)

/-- Any two distinct named labels have nonnegative fiber mass (SS, SB, BS, BB). -/
theorem mass_two_labels_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (a b : V) (hab : a ≠ b) (i j : V) :
    0 ≤ mass G s (fun π => π a = i ∧ π b = j) := by
  by_cases ha : ∃ k, a = s k <;> by_cases hb : ∃ l, b = s l
  · obtain ⟨k,rfl⟩ := ha
    obtain ⟨l,rfl⟩ := hb
    rw [mass_distinguished_pair G s hd hn k l (fun h => hab (congrArg s h))]
    apply div_nonneg _ (by positivity)
    unfold edge
    split_ifs <;> norm_num
  · obtain ⟨k,rfl⟩ := ha
    have hb' : b ∈ background s := by simpa only [mem_background, not_exists] using hb
    exact mass_mixed_nonneg G s hd hn k ⟨b,hb'⟩ i j
  · obtain ⟨l,rfl⟩ := hb
    have ha' : a ∈ background s := by simpa only [mem_background, not_exists] using ha
    simpa only [and_comm] using mass_mixed_nonneg G s hd hn l ⟨a,ha'⟩ j i
  · have ha' : a ∈ background s := by simpa only [mem_background, not_exists] using ha
    have hb' : b ∈ background s := by simpa only [mem_background, not_exists] using hb
    exact mass_background_pair_nonneg G s hd hn
      ⟨(⟨a,ha'⟩,⟨b,hb'⟩), fun h => hab (congrArg Subtype.val h)⟩ i j

/-- Full cylinder positivity: prescribe the positions of any set of at most
two named labels. Inconsistent prescriptions automatically have mass zero. -/
theorem mass_fixing_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3 ↪ V) (hd : ∀ i, G.degree i = 2) (hn : 6 ≤ Fintype.card V)
    (W : Finset V) (hW : W.card ≤ 2) (f : V → V) :
    0 ≤ mass G s (fun π => ∀ w ∈ W, π w = f w) := by
  have hc : W.card = 0 ∨ W.card = 1 ∨ W.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have hWe : W = ∅ := Finset.card_eq_zero.mp hc
    simp [hWe, mass, weight_total G s hd hn]
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hc
    simpa only [Finset.mem_singleton, forall_eq] using mass_label_nonneg G s hd hn a (f a)
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
    simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
      mass_two_labels_nonneg G s hd hn a b hab (f a) (f b)

end
end Lemmata.SpanningTreeSymmetricEF.PathLabeling
