module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FerrersDrift

@[expose] public section

/-!
# Survival bound for protected old rows

This module supplies the probability calculation behind the young/old record
bound.  It works by an explicit switching injection at each ascending rank.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- No rank strictly below `h` is assigned to a protected row. -/
def AvoidBelow {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) (sigma : FerrersPerm D) : Prop :=
  ∀ r, r < h → sigma.1.symm r ∉ P

/-- Protected rows also avoid rank `h`. -/
def AvoidThrough {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) (sigma : FerrersPerm D) : Prop :=
  AvoidBelow P h sigma ∧ sigma.1.symm h ∉ P

noncomputable def PreviousAssignments {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :=
  {sigma : FerrersPerm D // AvoidBelow P h sigma}

noncomputable def SurvivingAssignments {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :=
  {sigma : FerrersPerm D // AvoidThrough P h sigma}

noncomputable def HitAssignments {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :=
  {sigma : PreviousAssignments (D := D) P h // sigma.1.1.symm h ∈ P}

noncomputable instance fintypePrevious {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) : Fintype (PreviousAssignments (D := D) P h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance fintypeSurviving {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) : Fintype (SurvivingAssignments (D := D) P h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance fintypeHit {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) : Fintype (HitAssignments (D := D) P h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Survivors represented as previous assignments avoiding the current rank. -/
noncomputable def survivingEquiv {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :
    SurvivingAssignments (D := D) P h ≃
      {sigma : PreviousAssignments (D := D) P h // sigma.1.1.symm h ∉ P} where
  toFun s := ⟨⟨s.1, s.2.1⟩, s.2.2⟩
  invFun s := ⟨s.1.1, s.1.2, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Previous assignments partition into survivors and hits. -/
noncomputable def previousEquivSurviveOrHit {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :
    PreviousAssignments (D := D) P h ≃
      SurvivingAssignments (D := D) P h ⊕ HitAssignments (D := D) P h where
  toFun sigma := if hh : sigma.1.1.symm h ∈ P then
      Sum.inr ⟨sigma, hh⟩ else
      Sum.inl ⟨sigma.1, sigma.2, hh⟩
  invFun x := match x with
    | Sum.inl sigma => ⟨sigma.1, sigma.2.1⟩
    | Sum.inr sigma => sigma.1
  left_inv sigma := by
    by_cases hh : sigma.1.1.symm h ∈ P
    · simp only [dif_pos hh]
    · simp only [dif_neg hh]
      exact Subtype.ext (by rfl)
  right_inv x := by
    rcases x with sigma | sigma
    · simp [dite_eq_right sigma.2.2]
      rfl
    · simp [dite_eq_left sigma.2]
      rfl

lemma card_surviving_add_hit {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :
    Fintype.card (SurvivingAssignments (D := D) P h) +
      Fintype.card (HitAssignments (D := D) P h) =
        Fintype.card (PreviousAssignments (D := D) P h) := by
  rw [← Fintype.card_sum, Fintype.card_congr (previousEquivSurviveOrHit P h)]

/-- Complement of protected rows. -/
abbrev Unprotected {m : ℕ} (P : Finset (Fin m)) :=
  {i : Fin m // i ∉ P}

/-- The switch used in the one-step survival count. -/
noncomputable def survivalSwitch {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m)
    (heligible : ∀ p ∈ P, D.lower p ≤ h.val)
    (x : SurvivingAssignments (D := D) P h × {p : Fin m // p ∈ P}) :
    HitAssignments (D := D) P h × Unprotected P := by
  classical
  let sigma := x.1.1
  let p := x.2.1
  let r := sigma.1.symm h
  let s := sigma.1 p
  have hr_not : r ∉ P := x.1.2.2
  have hpr : p ≠ r := by
    intro heq
    apply hr_not
    rw [← heq]
    exact x.2.2
  have hs_ne : s ≠ h := by
    intro heq
    apply hpr
    exact sigma.1.injective (heq.trans (sigma.1.apply_symm_apply h).symm)
  have hhs : h < s := by
    rcases lt_or_gt_of_ne hs_ne with hsh | hhs
    · have hpnot := x.1.2.1 s hsh
      have hprow : sigma.1.symm s = p := sigma.1.symm_apply_apply p
      have hpmem : sigma.1.symm s ∈ P := by rw [hprow]; exact x.2.2
      exact (hpnot hpmem).elim
    · exact hhs
  let edge : DownEdge D := {
    source := sigma
    row := p
    lowerValue := h
    lower_allowed := heligible p x.2.2
    lower_lt := hhs }
  let target := edge.target
  have hprev : AvoidBelow P h target := by
    intro a ha
    have haneh : a ≠ h := ne_of_lt ha
    have hanes : a ≠ s := ne_of_lt (ha.trans hhs)
    have hval : target.1.symm a = sigma.1.symm a := by
      have hfix : (Equiv.swap h s) a = a :=
        Equiv.swap_apply_of_ne_of_ne haneh hanes
      have hval' : target.1 (sigma.1.symm a) = a := by
        simp [target, edge, DownEdge.target, swapValues, sigma, s, hfix]
      exact (Equiv.symm_apply_eq target.1).2 hval'.symm
    rw [hval]
    exact x.1.2.1 a ha
  have hhit : target.1.symm h ∈ P := by
    have hpval : target.1 p = h := by simp [target, edge, DownEdge.target]
    have hrow : target.1.symm h = p := (Equiv.symm_apply_eq target.1).2 hpval.symm
    rw [hrow]
    exact x.2.2
  exact (⟨⟨target, hprev⟩, hhit⟩, ⟨r, hr_not⟩)

/-- Decode the underlying source permutation and protected row. -/
noncomputable def decodeSurvivalSwitch {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) :
    (HitAssignments (D := D) P h × Unprotected P) →
      Equiv.Perm (Fin m) × Fin m := fun z =>
  let target := z.1.1.1
  let r := z.2.1
  (swapValues target.1 h (target.1 r), target.1.symm h)

lemma decode_survivalSwitch {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m)
    (heligible : ∀ p ∈ P, D.lower p ≤ h.val)
    (x : SurvivingAssignments (D := D) P h × {p : Fin m // p ∈ P}) :
    decodeSurvivalSwitch P h (survivalSwitch (D := D) P h heligible x) =
      (x.1.1.1, x.2.1) := by
  classical
  let sigma := x.1.1
  let p := x.2.1
  let r := sigma.1.symm h
  let s := sigma.1 p
  have hr : sigma.1 r = h := sigma.1.apply_symm_apply h
  have ht_r : (swapValues sigma.1 h s) r = s := by
    simp [swapValues, hr]
  have ht_p : (swapValues sigma.1 h s) p = h := by
    simp [swapValues, s]
  have hrecover : swapValues (swapValues sigma.1 h s) h s = sigma.1 :=
    swapValues_involutive _ _ _
  have hrow : (swapValues sigma.1 h s).symm h = p :=
    (Equiv.symm_apply_eq _).2 ht_p.symm
  change
    (swapValues (swapValues sigma.1 h s) h ((swapValues sigma.1 h s) r),
      (swapValues sigma.1 h s).symm h) = (sigma.1, p)
  rw [ht_r, hrecover, hrow]

/-- The survival switch is injective. -/
lemma survivalSwitch_injective {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m)
    (heligible : ∀ p ∈ P, D.lower p ≤ h.val) :
    Function.Injective (survivalSwitch (D := D) P h heligible) := by
  intro x y hxy
  have hd := congrArg (decodeSurvivalSwitch P h) hxy
  rw [decode_survivalSwitch P h heligible x,
    decode_survivalSwitch P h heligible y] at hd
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg Prod.fst hd
  · apply Subtype.ext
    exact congrArg Prod.snd hd

/-- One-step cardinal survival inequality. -/
theorem card_survival_step {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m)
    (heligible : ∀ p ∈ P, D.lower p ≤ h.val) :
    P.card * Fintype.card (SurvivingAssignments (D := D) P h) ≤
      (m - P.card) * Fintype.card (HitAssignments (D := D) P h) := by
  have hc := Fintype.card_le_of_injective (survivalSwitch (D := D) P h heligible)
    (survivalSwitch_injective (D := D) P h heligible)
  simp only [Fintype.card_prod, Fintype.card_coe] at hc
  have hcomp : Fintype.card (Unprotected P) = m - P.card := by
    simp [Unprotected]
  simpa [hcomp, Nat.mul_comm] using hc

/-- Equivalent recurrence form. -/
theorem card_survival_recurrence {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m)
    (heligible : ∀ p ∈ P, D.lower p ≤ h.val) :
    m * Fintype.card (SurvivingAssignments (D := D) P h) ≤
      (m - P.card) * Fintype.card (PreviousAssignments (D := D) P h) := by
  have hs := card_survival_step (D := D) P h heligible
  have hp := card_surviving_add_hit (D := D) P h
  have hPm : P.card ≤ m := by simpa using P.card_le_univ
  have hsplit : m - P.card + P.card = m := Nat.sub_add_cancel hPm
  calc
    m * Fintype.card (SurvivingAssignments (D := D) P h) =
        P.card * Fintype.card (SurvivingAssignments (D := D) P h) +
          (m - P.card) * Fintype.card (SurvivingAssignments (D := D) P h) := by
            nth_rewrite 1 [← hsplit]
            rw [Nat.add_mul, Nat.add_comm]
    _ ≤ (m - P.card) * Fintype.card (HitAssignments (D := D) P h) +
          (m - P.card) * Fintype.card (SurvivingAssignments (D := D) P h) :=
      Nat.add_le_add_right hs _
    _ = (m - P.card) * Fintype.card (PreviousAssignments (D := D) P h) := by
      rw [← Nat.mul_add, Nat.add_comm, hp]

/-- Survivors through `h` are exactly previous assignments before `h+1`. -/
noncomputable def surviveEquivNext {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (h : Fin m) (hh : h.val + 1 < m) :
    SurvivingAssignments (D := D) P h ≃
      PreviousAssignments (D := D) P ⟨h.val + 1, hh⟩ where
  toFun sigma := ⟨sigma.1, by
    intro r hr
    have hrle : r ≤ h := by exact_mod_cast (Nat.lt_succ_iff.mp hr)
    rcases hrle.eq_or_lt with rfl | hrlt
    · exact sigma.2.2
    · exact sigma.2.1 r hrlt⟩
  invFun sigma := ⟨sigma.1, by
    constructor
    · intro r hr
      exact sigma.2 r (hr.trans (by exact_mod_cast Nat.lt_succ_self h.val))
    · exact sigma.2 h (by exact_mod_cast Nat.lt_succ_self h.val)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Iteration of a multiplicative survival recurrence. -/
theorem iterate_survival_recurrence
    (m j A : ℕ) (N : ℕ → ℕ)
    (hrec : ∀ k < A, m * N (k + 1) ≤ (m - j) * N k) :
    m ^ A * N A ≤ (m - j) ^ A * N 0 := by
  induction A with
  | zero => simp
  | succ A ih =>
      have hlast := hrec A (Nat.lt_succ_self A)
      have hprev : ∀ k < A, m * N (k + 1) ≤ (m - j) * N k :=
        fun k hk => hrec k (hk.trans (Nat.lt_succ_self A))
      have hih := ih hprev
      calc
        m ^ (A + 1) * N (A + 1) = m ^ A * (m * N (A + 1)) := by ring
        _ ≤ m ^ A * ((m - j) * N A) := Nat.mul_le_mul_left _ hlast
        _ = (m - j) * (m ^ A * N A) := by ring
        _ ≤ (m - j) * ((m - j) ^ A * N 0) := Nat.mul_le_mul_left _ hih
        _ = (m - j) ^ (A + 1) * N 0 := by ring

/-- Cardinal survival bound across a consecutive rank window. -/
theorem card_avoid_window {m : ℕ} {D : FerrersData m}
    (P : Finset (Fin m)) (start A : ℕ)
    (hbound : start + A < m)
    (heligible : ∀ p ∈ P, D.lower p ≤ start) :
    m ^ A * Fintype.card
        (PreviousAssignments (D := D) P ⟨start + A, hbound⟩) ≤
      (m - P.card) ^ A * Fintype.card
        (PreviousAssignments (D := D) P ⟨start, lt_of_le_of_lt
          (Nat.le_add_right start A) hbound⟩) := by
  let N : ℕ → ℕ := fun k =>
    if hk : start + k < m then
      Fintype.card (PreviousAssignments (D := D) P ⟨start + k, hk⟩)
    else 0
  have hrec : ∀ k < A, m * N (k + 1) ≤ (m - P.card) * N k := by
    intro k hk
    have hk0 : start + k < m := lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.le_of_lt hk) start) hbound
    have hk1 : start + (k + 1) < m := by omega
    have hfin : (⟨start + k, hk0⟩ : Fin m).val + 1 < m := by omega
    have hcardEq := Fintype.card_congr
      (surviveEquivNext (D := D) P ⟨start + k, hk0⟩ hfin)
    have hstep := card_survival_recurrence (D := D) P ⟨start + k, hk0⟩
      (fun p hp => by
        change D.lower p ≤ start + k
        exact (heligible p hp).trans (Nat.le_add_right start k))
    dsimp [N]
    rw [dif_pos hk0, dif_pos hk1]
    have hcardEq' : Fintype.card
        (SurvivingAssignments (D := D) P ⟨start + k, hk0⟩) =
        Fintype.card (PreviousAssignments (D := D) P ⟨start + (k + 1), hk1⟩) := by
      simpa only [Nat.add_assoc] using hcardEq
    rw [← hcardEq']
    exact hstep
  have hiter := iterate_survival_recurrence m P.card A N hrec
  have hstart : start < m := lt_of_le_of_lt (Nat.le_add_right start A) hbound
  simpa [N, hbound, hstart] using hiter

/-- Tangent lower bound for a positive integer power. -/
lemma pow_increment_lower (x h : ℝ) (A : ℕ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ((A + 1 : ℕ) : ℝ) * h * x ^ A ≤
      (x + h) ^ (A + 1) - x ^ (A + 1) := by
  induction A with
  | zero => norm_num
  | succ A ih =>
      have hdiff : 0 ≤ (x + h) ^ (A + 1) - x ^ (A + 1) := by
        exact sub_nonneg.mpr (pow_le_pow_left₀ hx (by linarith) _)
      have h1 := mul_le_mul_of_nonneg_left ih hx
      have h2 := mul_le_mul_of_nonneg_right
        (show x ≤ x + h by linarith) hdiff
      calc
        (((A + 1) + 1 : ℕ) : ℝ) * h * x ^ (A + 1) =
            x * ((((A + 1 : ℕ) : ℝ) * h * x ^ A)) + h * x ^ (A + 1) := by
              push_cast
              ring
        _ ≤ x * ((x + h) ^ (A + 1) - x ^ (A + 1)) + h * x ^ (A + 1) :=
          add_le_add_left h1 _
        _ ≤ (x + h) * ((x + h) ^ (A + 1) - x ^ (A + 1)) +
            h * x ^ (A + 1) := add_le_add_left h2 _
        _ = (x + h) ^ ((A + 1) + 1) - x ^ ((A + 1) + 1) := by ring

/-- Discrete power sum bounded by its telescoping integral majorant. -/
theorem sum_power_ratio_le (m A : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.range m, ((j : ℝ) / m) ^ A) ≤
      (m : ℝ) / (A + 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ℝ := (m : ℝ) / (A + 1)
  let f : ℕ → ℝ := fun j => ((j : ℝ) / m) ^ (A + 1)
  have hpoint : ∀ j < m,
      ((j : ℝ) / m) ^ A ≤ c * (f (j + 1) - f j) := by
    intro j hj
    have ht := pow_increment_lower ((j : ℝ) / m) (1 / m) A
      (by positivity) (by positivity)
    have hcoef : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) * (1 / m) := by positivity
    have htord : ((j : ℝ) / m) ^ A *
        (((A + 1 : ℕ) : ℝ) * (1 / m)) ≤
        ((j : ℝ) / m + 1 / m) ^ (A + 1) - ((j : ℝ) / m) ^ (A + 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using ht
    have ht' := (le_div_iff₀ hcoef).2 htord
    have hbase : (j : ℝ) / m + 1 / m = ((j + 1 : ℕ) : ℝ) / m := by
      push_cast
      field_simp [hmR.ne']
    dsimp [c, f]
    calc
      ((j : ℝ) / m) ^ A ≤
          (((j : ℝ) / m + 1 / m) ^ (A + 1) -
            ((j : ℝ) / m) ^ (A + 1)) /
              (((A + 1 : ℕ) : ℝ) * (1 / m)) := ht'
      _ = ((m : ℝ) / (A + 1)) *
          ((((j + 1 : ℕ) : ℝ) / m) ^ (A + 1) -
            ((j : ℝ) / m) ^ (A + 1)) := by
            rw [← hbase]
            push_cast
            field_simp [hmR.ne']
  calc
    (∑ j ∈ Finset.range m, ((j : ℝ) / m) ^ A) ≤
        ∑ j ∈ Finset.range m, c * (f (j + 1) - f j) :=
      Finset.sum_le_sum (fun j hj => hpoint j (Finset.mem_range.mp hj))
    _ = c * (f m - f 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ (m : ℝ) / (A + 1) := by
      dsimp [c, f]
      have hpow : ((m : ℝ) / m) ^ (A + 1) = 1 := by
        field_simp [hmR.ne']
        norm_num
      rw [hpow]
      norm_num

/-- Aggregate the window-survival bounds over old-row priority ranks. -/
theorem aggregate_old_survival
    (m A N : ℕ) (hm : 0 < m) (hN : 0 < N)
    (count : Fin m → ℕ)
    (hcount : ∀ j,
      m ^ A * count j ≤ m * (m - (j.val + 1)) ^ A * N) :
    (∑ j, (count j : ℝ)) / N ≤ (m : ℝ) ^ 2 / (A + 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpoint : ∀ j : Fin m,
      (count j : ℝ) / N ≤
        (m : ℝ) * (((m - (j.val + 1) : ℕ) : ℝ) / m) ^ A := by
    intro j
    have hc : (m : ℝ) ^ A * count j ≤
        (m : ℝ) * ((m - (j.val + 1) : ℕ) : ℝ) ^ A * N := by
      exact_mod_cast hcount j
    apply (div_le_iff₀ hNR).2
    have hmpow : 0 < (m : ℝ) ^ A := pow_pos hmR _
    have hc' : (count j : ℝ) * (m : ℝ) ^ A ≤
        (m : ℝ) * ((m - (j.val + 1) : ℕ) : ℝ) ^ A * N := by
      simpa [mul_comm] using hc
    have hcdiv := (le_div_iff₀ hmpow).2 hc'
    calc
      (count j : ℝ) ≤
          ((m : ℝ) * ((m - (j.val + 1) : ℕ) : ℝ) ^ A * N) /
            (m : ℝ) ^ A := hcdiv
      _ = (m : ℝ) * (((m - (j.val + 1) : ℕ) : ℝ) / m) ^ A * N := by
        rw [div_pow]
        ring
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hpoint j)
  rw [← Finset.sum_div, ← Finset.mul_sum] at hsum
  have hrev :
      (∑ j : Fin m, (((m - (j.val + 1) : ℕ) : ℝ) / m) ^ A) =
        ∑ j : Fin m, ((j.val : ℝ) / m) ^ A := by
    have he := Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => ((j.val : ℝ) / m) ^ A)
    simpa [Fin.val_rev] using he
  rw [hrev] at hsum
  have hfin : (∑ j : Fin m, ((j.val : ℝ) / m) ^ A) =
      ∑ j ∈ Finset.range m, ((j : ℝ) / m) ^ A := by
    exact Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ) / m) ^ A) m
  rw [hfin] at hsum
  have hpowers := sum_power_ratio_le m A hm
  have hmul := mul_le_mul_of_nonneg_left hpowers (show (0 : ℝ) ≤ m by positivity)
  exact hsum.trans (hmul.trans (by ring_nf; exact le_rfl))

/-- Young/old arithmetic once record cells have been grouped by priority. -/
theorem young_old_from_grouped_counts
    (m A N young old : ℕ) (hm : 0 < m) (hA : 0 < A) (hN : 0 < N)
    (count : Fin m → ℕ)
    (hyoung : young ≤ N * m * A)
    (hold : old = ∑ j, count j)
    (hcount : ∀ j,
      m ^ A * count j ≤ m * (m - (j.val + 1)) ^ A * N) :
    ((young + old : ℕ) : ℝ) / N ≤
      (m : ℝ) * A + (m : ℝ) ^ 2 / A := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hyR : (young : ℝ) ≤ (N : ℝ) * m * A := by exact_mod_cast hyoung
  have hy : (young : ℝ) / N ≤ (m : ℝ) * A := by
    apply (div_le_iff₀ hNR).2
    nlinarith
  have ho := aggregate_old_survival m A N hm hN count hcount
  have holdR : (old : ℝ) = ∑ j, (count j : ℝ) := by exact_mod_cast hold
  have hmA : (m : ℝ) ^ 2 / (A + 1) ≤ (m : ℝ) ^ 2 / A :=
    div_le_div_of_nonneg_left (sq_nonneg _) hAR (by linarith)
  rw [Nat.cast_add, holdR, add_div]
  linarith

/-! ## Priority records and deterministic young contribution -/

/-- Record pairs for a fixed total row priority (smaller priority value means
earlier in the query order). -/
def PriorityRecord {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) :=
  {x : FerrersPerm D × Fin m × Fin m //
    D.lower x.2.1 ≤ x.2.2.val ∧
      ∀ k, x.1.1 k < x.2.2 → priority x.2.1 < priority k}

noncomputable instance {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) : Fintype (PriorityRecord D priority) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Query-magnitude records embed in records for any compatible total priority. -/
noncomputable def recordToPriority {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (priority : Equiv.Perm (Fin m))
    (hpriority : ∀ i k, Q.q k < Q.q i → priority i < priority k)
    (r : QueryRanks.RecordCell Q) : PriorityRecord D priority :=
  ⟨r.1, r.2.1, fun k hk => hpriority _ _ (r.2.2 k hk)⟩

lemma recordToPriority_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (priority : Equiv.Perm (Fin m))
    (hpriority : ∀ i k, Q.q k < Q.q i → priority i < priority k) :
    Function.Injective (recordToPriority Q priority hpriority) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : PriorityRecord D priority => z.1) h

/-- Young records: the value lies fewer than `A` positions above the row's
lower bound. -/
def YoungPriorityRecord {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :=
  {r : PriorityRecord D priority // r.1.2.2.val < D.lower r.1.2.1 + A}

noncomputable instance {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    Fintype (YoungPriorityRecord D priority A) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Inject young records into `(assignment,row,offset<A)`. -/
noncomputable def youngRecordCode {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} :
    YoungPriorityRecord D priority A → FerrersPerm D × Fin m × Fin A := fun r =>
  (r.1.1.1, r.1.1.2.1, ⟨r.1.1.2.2.val - D.lower r.1.1.2.1, by
    have hlo := r.1.2.1
    have hy := r.2
    omega⟩)

lemma youngRecordCode_injective {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} :
    Function.Injective (youngRecordCode D priority (A := A)) := by
  intro x y h
  have hs := congrArg (fun z => z.1) h
  have hr := congrArg (fun z => z.2.1) h
  have ho := congrArg (fun z => z.2.2.val) h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hs
  · apply Prod.ext
    · exact hr
    · apply Fin.ext
      have hxlo := x.1.2.1
      have hylo := y.1.2.1
      have hlower : D.lower x.1.1.2.1 = D.lower y.1.1.2.1 :=
        congrArg D.lower hr
      have hxoff : x.1.1.2.2.val - D.lower x.1.1.2.1 +
          D.lower x.1.1.2.1 = x.1.1.2.2.val := Nat.sub_add_cancel hxlo
      have hyoff : y.1.1.2.2.val - D.lower y.1.1.2.1 +
          D.lower y.1.1.2.1 = y.1.1.2.2.val := Nat.sub_add_cancel hylo
      simp only [youngRecordCode] at ho
      omega

/-- Deterministic young-record cardinal bound. -/
theorem card_youngPriorityRecord_le {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} :
    Fintype.card (YoungPriorityRecord D priority A) ≤
      Fintype.card (FerrersPerm D) * m * A := by
  have hc := Fintype.card_le_of_injective (youngRecordCode D priority (A := A))
    (youngRecordCode_injective D priority (A := A))
  simpa [Fintype.card_prod, Nat.mul_assoc] using hc

end Lemmata.DistributionalLowerBounds.Core.Distributional
