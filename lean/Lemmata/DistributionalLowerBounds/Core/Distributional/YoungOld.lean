module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.RecordSurvival

@[expose] public section

/-! Final grouping step for the young/old record bound. -/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Old records have at least `A` rank positions between their lower bound and
record value. -/
def OldPriorityRecord {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :=
  {r : PriorityRecord D priority // D.lower r.1.2.1 + A ≤ r.1.2.2.val}

noncomputable instance {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    Fintype (OldPriorityRecord D priority A) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Old rows before a given row in priority order. -/
def protectedRows {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) (a i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun k => D.lower k + A ≤ a.val ∧ priority k ≤ priority i

lemma self_mem_protectedRows {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} {a i : Fin m}
    (hold : D.lower i + A ≤ a.val) :
    i ∈ protectedRows D priority A a i := by
  simp [protectedRows, hold]

lemma protectedRows_card_pos {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} {a i : Fin m}
    (hold : D.lower i + A ≤ a.val) :
    0 < (protectedRows D priority A a i).card :=
  Finset.card_pos.mpr ⟨i, self_mem_protectedRows D priority hold⟩

lemma protectedRows_card_le {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) (a i : Fin m) :
    (protectedRows D priority A a i).card ≤ m := by
  simpa using (protectedRows D priority A a i).card_le_univ

/-- Priority-prefix cardinal uniquely identifies an old row. -/
lemma protectedRows_card_injective {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} {a i k : Fin m}
    (hi : D.lower i + A ≤ a.val) (hk : D.lower k + A ≤ a.val)
    (hcard : (protectedRows D priority A a i).card =
      (protectedRows D priority A a k).card) : i = k := by
  apply priority.injective
  rcases lt_trichotomy (priority i) (priority k) with hlt | heq | hgt
  · have hsub : protectedRows D priority A a i ⊆
        protectedRows D priority A a k := by
      intro x hx
      simp [protectedRows] at hx ⊢
      exact ⟨hx.1, hx.2.trans hlt.le⟩
    have hkMem : k ∈ protectedRows D priority A a k :=
      self_mem_protectedRows D priority hk
    have hkNot : k ∉ protectedRows D priority A a i := by
      simp [protectedRows, hk, not_le_of_gt hlt]
    have hne : protectedRows D priority A a i ≠
        protectedRows D priority A a k := by
      intro h
      apply hkNot
      rw [h]
      exact hkMem
    have hltcard := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega
  · exact heq
  · have hsub : protectedRows D priority A a k ⊆
        protectedRows D priority A a i := by
      intro x hx
      simp [protectedRows] at hx ⊢
      exact ⟨hx.1, hx.2.trans hgt.le⟩
    have hiMem : i ∈ protectedRows D priority A a i :=
      self_mem_protectedRows D priority hi
    have hiNot : i ∉ protectedRows D priority A a k := by
      simp [protectedRows, hi, not_le_of_gt hgt]
    have hne : protectedRows D priority A a k ≠
        protectedRows D priority A a i := by
      intro h
      apply hiNot
      rw [h]
      exact hiMem
    have hltcard := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega

/-- Zero-based protected-prefix index. -/
def oldPriorityIndex {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ}
    (r : OldPriorityRecord D priority A) : Fin m :=
  ⟨(protectedRows D priority A r.1.1.2.2 r.1.1.2.1).card - 1, by
    have hp := protectedRows_card_pos D priority r.2
    have hl := protectedRows_card_le D priority A r.1.1.2.2 r.1.1.2.1
    omega⟩

/-- Old records grouped by value and protected-prefix index. -/
def OldRecordGroup {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) (a j : Fin m) :=
  {r : OldPriorityRecord D priority A //
    r.1.1.2.2 = a ∧ oldPriorityIndex D priority r = j}

noncomputable instance {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) (a j : Fin m) :
    Fintype (OldRecordGroup D priority A a j) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- All records in one nonempty group use the same row. -/
lemma row_eq_of_same_oldGroup {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} {a j : Fin m}
    (x y : OldRecordGroup D priority A a j) :
    x.1.1.1.2.1 = y.1.1.1.2.1 := by
  have hxval : x.1.1.1.2.2 = a := x.2.1
  have hyval : y.1.1.1.2.2 = a := y.2.1
  have hxidx := congrArg Fin.val x.2.2
  have hyidx := congrArg Fin.val y.2.2
  dsimp [oldPriorityIndex] at hxidx hyidx
  have hxp := protectedRows_card_pos D priority x.1.2
  have hyp := protectedRows_card_pos D priority y.1.2
  have hxraw : (protectedRows D priority A x.1.1.1.2.2 x.1.1.1.2.1).card =
      j.val + 1 := by omega
  have hyraw : (protectedRows D priority A y.1.1.1.2.2 y.1.1.1.2.1).card =
      j.val + 1 := by omega
  have hxmove := congrArg
    (fun z : Fin m => (protectedRows D priority A z x.1.1.1.2.1).card) hxval
  have hymove := congrArg
    (fun z : Fin m => (protectedRows D priority A z y.1.1.1.2.1).card) hyval
  have hxcard : (protectedRows D priority A a x.1.1.1.2.1).card = j.val + 1 :=
    hxmove.symm.trans hxraw
  have hycard : (protectedRows D priority A a y.1.1.1.2.1).card = j.val + 1 :=
    hymove.symm.trans hyraw
  have hcard : (protectedRows D priority A a x.1.1.1.2.1).card =
      (protectedRows D priority A a y.1.1.1.2.1).card := by omega
  have hyold : D.lower y.1.1.1.2.1 + A ≤ a.val := by
    simpa [hyval] using y.1.2
  have hxold : D.lower x.1.1.1.2.1 + A ≤ a.val := by
    simpa [hxval] using x.1.2
  exact protectedRows_card_injective D priority hxold hyold hcard

/-- A priority record avoids all protected rows below its value. -/
lemma oldRecord_avoids {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ}
    (r : OldPriorityRecord D priority A) :
    AvoidBelow (protectedRows D priority A r.1.1.2.2 r.1.1.2.1)
      r.1.1.2.2 r.1.1.1 := by
  intro a ha hmem
  have hp := (Finset.mem_filter.mp hmem).2.2
  have hrec := r.1.2.2 (r.1.1.1.1.symm a) (by simpa using ha)
  exact (not_lt_of_ge hp hrec)

/-- Cardinal survival bound for one `(value, priority-index)` old group. -/
theorem card_oldRecordGroup_bound {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} (a j : Fin m) :
    m ^ A * Fintype.card (OldRecordGroup D priority A a j) ≤
      (m - (j.val + 1)) ^ A * Fintype.card (FerrersPerm D) := by
  rcases isEmpty_or_nonempty (OldRecordGroup D priority A a j) with hempty | hnonempty
  · letI := hempty
    rw [Fintype.card_eq_zero]
    simp
  · let x0 : OldRecordGroup D priority A a j := Classical.choice hnonempty
    let i0 : Fin m := x0.1.1.1.2.1
    let P : Finset (Fin m) := protectedRows D priority A a i0
    have hAlea : A ≤ a.val := by
      have hold := x0.1.2
      have hval := congrArg Fin.val x0.2.1
      omega
    let start : ℕ := a.val - A
    have hstart : start + A = a.val := Nat.sub_add_cancel hAlea
    have hbound : start + A < m := by rw [hstart]; exact a.isLt
    have hPcard : P.card = j.val + 1 := by
      have hidx := congrArg Fin.val x0.2.2
      dsimp [oldPriorityIndex] at hidx
      have hp := protectedRows_card_pos D priority x0.1.2
      have hval := x0.2.1
      have hmove := congrArg
        (fun z : Fin m => (protectedRows D priority A z i0).card) hval
      dsimp [P, i0]
      dsimp [i0] at hmove
      omega
    have heligible : ∀ p ∈ P, D.lower p ≤ start := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      dsimp [start]
      omega
    let toPrev : OldRecordGroup D priority A a j →
        PreviousAssignments (D := D) P a := fun x => ⟨x.1.1.1.1, by
      intro r hr hmem
      have hp := (Finset.mem_filter.mp hmem).2.2
      have hrow := row_eq_of_same_oldGroup D priority x x0
      have hval : x.1.1.1.2.2 = a := x.2.1
      have hrank : x.1.1.1.1.1 (x.1.1.1.1.1.symm r) < x.1.1.1.2.2 := by
        simpa [hval] using hr
      have hrec := x.1.1.2.2 (x.1.1.1.1.1.symm r) hrank
      rw [hrow] at hrec
      exact (not_lt_of_ge hp hrec)⟩
    have htoPrev : Function.Injective toPrev := by
      intro x y hxy
      have hsigma : x.1.1.1.1 = y.1.1.1.1 := congrArg Subtype.val hxy
      have hrowx := row_eq_of_same_oldGroup D priority x x0
      have hrowy := row_eq_of_same_oldGroup D priority y x0
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hsigma
      · apply Prod.ext
        · exact hrowx.trans hrowy.symm
        · exact x.2.1.trans y.2.1.symm
    have hgroupCard := Fintype.card_le_of_injective toPrev htoPrev
    have hwindow := card_avoid_window (D := D) P start A hbound heligible
    have haendpoint : a = (⟨start + A, hbound⟩ : Fin m) := by
      apply Fin.ext
      simpa using hstart.symm
    have hendpoint : Fintype.card (PreviousAssignments (D := D) P a) =
        Fintype.card (PreviousAssignments (D := D) P ⟨start + A, hbound⟩) :=
      congrArg (fun z : Fin m =>
        Fintype.card (PreviousAssignments (D := D) P z)) haendpoint
    rw [← hendpoint] at hwindow
    have hstartCard : Fintype.card
        (PreviousAssignments (D := D) P ⟨start,
          lt_of_le_of_lt (Nat.le_add_right start A) hbound⟩) ≤
        Fintype.card (FerrersPerm D) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    calc
      m ^ A * Fintype.card (OldRecordGroup D priority A a j) ≤
          m ^ A * Fintype.card (PreviousAssignments (D := D) P a) :=
        Nat.mul_le_mul_left _ hgroupCard
      _ ≤ (m - P.card) ^ A * Fintype.card
          (PreviousAssignments (D := D) P ⟨start,
            lt_of_le_of_lt (Nat.le_add_right start A) hbound⟩) := hwindow
      _ ≤ (m - P.card) ^ A * Fintype.card (FerrersPerm D) :=
        Nat.mul_le_mul_left _ hstartCard
      _ = (m - (j.val + 1)) ^ A * Fintype.card (FerrersPerm D) := by
        rw [hPcard]

/-- Decompose all old records by value and protected-prefix index. -/
noncomputable def oldRecordGroupEquiv {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    OldPriorityRecord D priority A ≃
      Σ a : Fin m, Σ j : Fin m, OldRecordGroup D priority A a j where
  toFun r := ⟨r.1.1.2.2, oldPriorityIndex D priority r, r, rfl, rfl⟩
  invFun r := r.2.2.1
  left_inv _ := rfl
  right_inv r := by rcases r with ⟨a, j, r, rfl, rfl⟩; rfl

lemma card_oldPriorityRecord_eq_sum {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    Fintype.card (OldPriorityRecord D priority A) =
      ∑ j : Fin m, ∑ a : Fin m,
        Fintype.card (OldRecordGroup D priority A a j) := by
  rw [Fintype.card_congr (oldRecordGroupEquiv D priority A),
    Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  rw [Finset.sum_comm]

/-- Priority records split into young and old records. -/
noncomputable def priorityRecordYoungOldEquiv {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    PriorityRecord D priority ≃
      YoungPriorityRecord D priority A ⊕ OldPriorityRecord D priority A where
  toFun r := if h : r.1.2.2.val < D.lower r.1.2.1 + A then
      Sum.inl ⟨r, h⟩ else Sum.inr ⟨r, Nat.le_of_not_gt h⟩
  invFun r := match r with | Sum.inl r => r.1 | Sum.inr r => r.1
  left_inv r := by by_cases h : r.1.2.2.val < D.lower r.1.2.1 + A <;> simp [h]
  right_inv r := by
    rcases r with r | r
    · simp [r.2]
      rfl
    · simp [Nat.not_lt_of_ge r.2]
      rfl

lemma card_priority_eq_young_add_old {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) (A : ℕ) :
    Fintype.card (PriorityRecord D priority) =
      Fintype.card (YoungPriorityRecord D priority A) +
        Fintype.card (OldPriorityRecord D priority A) := by
  rw [Fintype.card_congr (priorityRecordYoungOldEquiv D priority A),
    Fintype.card_sum]

/-- Fully assembled young/old record bound. -/
theorem card_priorityRecord_bound {m : ℕ} (D : FerrersData m)
    (priority : Equiv.Perm (Fin m)) {A : ℕ} (hm : 0 < m) (hA : 0 < A) :
    (Fintype.card (PriorityRecord D priority) : ℝ) /
        Fintype.card (FerrersPerm D) ≤
      (m : ℝ) * A + (m : ℝ) ^ 2 / A := by
  let N := Fintype.card (FerrersPerm D)
  let young := Fintype.card (YoungPriorityRecord D priority A)
  let old := Fintype.card (OldPriorityRecord D priority A)
  let count : Fin m → ℕ := fun j =>
    ∑ a : Fin m, Fintype.card (OldRecordGroup D priority A a j)
  have hN : 0 < N := Fintype.card_pos
  have hyoung : young ≤ N * m * A := by
    dsimp [young, N]
    exact card_youngPriorityRecord_le D priority
  have hold : old = ∑ j, count j := by
    dsimp [old, count]
    exact card_oldPriorityRecord_eq_sum D priority A
  have hcount : ∀ j,
      m ^ A * count j ≤ m * (m - (j.val + 1)) ^ A * N := by
    intro j
    dsimp [count, N]
    rw [Finset.mul_sum]
    calc
      (∑ a : Fin m, m ^ A *
          Fintype.card (OldRecordGroup D priority A a j)) ≤
          ∑ _a : Fin m,
            (m - (j.val + 1)) ^ A * Fintype.card (FerrersPerm D) :=
        Finset.sum_le_sum (fun a _ => card_oldRecordGroup_bound D priority a j)
      _ = m * (m - (j.val + 1)) ^ A * Fintype.card (FerrersPerm D) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        simp only [Fintype.card_fin]
        simp [Nat.mul_assoc]
  have hyold := young_old_from_grouped_counts m A N young old hm hA hN
    count hyoung hold hcount
  have hpartition := card_priority_eq_young_add_old D priority A
  dsimp [young, old, N] at hyold ⊢
  rw [hpartition]
  exact hyold

/-- Query-defined record proxy inherits the same bound. -/
theorem card_queryRecord_bound {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (priority : Equiv.Perm (Fin m))
    (hpriority : ∀ i k, Q.q k < Q.q i → priority i < priority k)
    {A : ℕ} (hm : 0 < m) (hA : 0 < A) :
    (Fintype.card (QueryRanks.RecordCell Q) : ℝ) /
        Fintype.card (FerrersPerm D) ≤
      (m : ℝ) * A + (m : ℝ) ^ 2 / A := by
  have hc := Fintype.card_le_of_injective
    (recordToPriority Q priority hpriority)
    (recordToPriority_injective Q priority hpriority)
  have hN : (0 : ℝ) < Fintype.card (FerrersPerm D) := card_cast_pos
  have hcR : (Fintype.card (QueryRanks.RecordCell Q) : ℝ) ≤
      Fintype.card (PriorityRecord D priority) := by exact_mod_cast hc
  have hdiv := div_le_div_of_nonneg_right hcR hN.le
  exact hdiv.trans (card_priorityRecord_bound D priority hm hA)

/-- Priority permutation induced by decreasing query magnitude. -/
noncomputable def queryPriority {m : ℕ} (q : Fin m → ℝ) :
    Equiv.Perm (Fin m) := (Tuple.sort (fun i => -q i)).symm

lemma queryPriority_compatible {m : ℕ} (q : Fin m → ℝ) (i k : Fin m)
    (h : q k < q i) : queryPriority q i < queryPriority q k := by
  let order := Tuple.sort (fun i => -q i)
  let pi := order.symm i
  let pk := order.symm k
  have hkey : -(q i) < -(q k) := by linarith
  have hmono := Tuple.monotone_sort (fun i => -q i)
  have hnot : ¬pk ≤ pi := by
    intro hle
    have hm := hmono hle
    have hm' : q i ≤ q k := by
      simpa [Function.comp_def, pi, pk, order] using hm
    linarith
  exact lt_of_not_ge hnot

/-- Query record bound with the square-root choice of `A`. -/
theorem card_queryRecord_sqrt_bound {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (hm : 0 < m) :
    (Fintype.card (QueryRanks.RecordCell Q) : ℝ) /
        Fintype.card (FerrersPerm D) ≤
      2 * (m : ℝ) * Real.sqrt m + m := by
  let A : ℕ := Nat.ceil (Real.sqrt (m : ℝ))
  have hspos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hA : 0 < A := Nat.ceil_pos.2 hspos
  have hbase := card_queryRecord_bound Q (queryPriority Q.q)
    (fun i k h => queryPriority_compatible Q.q i k h) hm hA
  have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hAge : Real.sqrt (m : ℝ) ≤ (A : ℝ) := Nat.le_ceil _
  have hAlt : (A : ℝ) < Real.sqrt (m : ℝ) + 1 := Nat.ceil_lt_add_one hs0
  have hAposR : (0 : ℝ) < A := by exact_mod_cast hA
  have hfirst : (m : ℝ) * A ≤ (m : ℝ) * Real.sqrt m + m := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hAlt.le hm0]
  have hsecond : (m : ℝ) ^ 2 / A ≤ (m : ℝ) * Real.sqrt m := by
    apply (div_le_iff₀ hAposR).2
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hsMul := mul_le_mul_of_nonneg_left hAge
      (mul_nonneg hm0 hs0)
    nlinarith
  linarith

/-- Full one-query cut-edge bound. -/
theorem card_waterCutEdge_sqrt_bound {m : ℕ} {D : FerrersData m}
    (W : QueryRanks.WaterQuery D) (hm : 0 < m) :
    (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) /
        Fintype.card (FerrersPerm D) ≤
      8 * (m : ℝ) * Real.sqrt m := by
  have hcut := QueryRanks.card_waterCutEdge_le W
  have hrec := card_queryRecord_sqrt_bound W.toQueryRanks hm
  have hN : (0 : ℝ) < Fintype.card (FerrersPerm D) := card_cast_pos
  have hcutR : (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) ≤
      2 * m * Fintype.card (FerrersPerm D) +
        2 * Fintype.card (QueryRanks.RecordCell W.toQueryRanks) := by
    exact_mod_cast hcut
  have hdiv : (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) /
      Fintype.card (FerrersPerm D) ≤
        2 * (m : ℝ) + 2 *
          ((Fintype.card (QueryRanks.RecordCell W.toQueryRanks) : ℝ) /
            Fintype.card (FerrersPerm D)) := by
    apply (div_le_iff₀ hN).2
    calc
      (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) ≤
          2 * m * Fintype.card (FerrersPerm D) +
            2 * Fintype.card (QueryRanks.RecordCell W.toQueryRanks) := hcutR
      _ = (2 * (m : ℝ) + 2 *
          ((Fintype.card (QueryRanks.RecordCell W.toQueryRanks) : ℝ) /
            Fintype.card (FerrersPerm D))) *
              Fintype.card (FerrersPerm D) := by
        field_simp [hN.ne']
  have hs : (1 : ℝ) ≤ Real.sqrt m := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m), Real.sqrt_nonneg (m : ℝ)]
  nlinarith

noncomputable instance waterAnswerDecEq (m : ℕ) :
    DecidableEq (QueryRanks.WaterQuery.Answer m) := Classical.decEq _

/-- Cut edges are the sigma type of cut outgoing edges by source. -/
noncomputable def waterCutEdgeSigmaEquiv {m : ℕ} {D : FerrersData m}
    (W : QueryRanks.WaterQuery D) :
    QueryRanks.WaterCutEdge W ≃
      Σ sigma : FerrersPerm D,
        {e : DownEdge.Outgoing D sigma //
          DownEdge.IsCut W.answer e.1} where
  toFun e := ⟨e.1.source, ⟨⟨e.1, rfl⟩, e.2⟩⟩
  invFun e := ⟨e.2.1.1, e.2.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨sigma, ⟨⟨e, he⟩, hc⟩⟩
    cases he
    rfl

lemma card_waterCutEdge_eq_sum {m : ℕ} {D : FerrersData m}
    (W : QueryRanks.WaterQuery D) :
    Fintype.card (QueryRanks.WaterCutEdge W) =
      ∑ sigma, DownEdge.cutOutdegree W.answer sigma := by
  rw [Fintype.card_congr (waterCutEdgeSigmaEquiv W), Fintype.card_sigma]
  rfl

/-- The complete `8 m^(3/2)` one-query deficit drift theorem. -/
theorem oneQuery_expected_deficit_drop {m : ℕ} {D : FerrersData m}
    (W : QueryRanks.WaterQuery D) (hm : 0 < m) :
    uniformAverage (fun sigma =>
      (DownEdge.natDeficit D : ℝ) -
        DownEdge.internalOutdegree W.answer sigma) ≤
      8 * (m : ℝ) * Real.sqrt m := by
  rw [DownEdge.edge_boundary_identity]
  have hcard := card_waterCutEdge_eq_sum W
  have hcardR : (Fintype.card (QueryRanks.WaterCutEdge W) : ℝ) =
      ∑ sigma, (DownEdge.cutOutdegree W.answer sigma : ℝ) := by
    exact_mod_cast hcard
  rw [← hcardR]
  exact card_waterCutEdge_sqrt_bound W hm

/-- Top-level composition from per-step mean deficits to the concrete
expected-loss lower bound.  An adaptive-method wrapper only has to instantiate
`deltaMean` and discharge `hstep` by conditional use of
`oneQuery_expected_deficit_drop`. -/
theorem concrete_distributional_lower_bound_from_steps
    {Omega : Type*} [Fintype Omega]
    (P : FinitePMF Omega) (Delta loss : Omega → ℝ)
    (deltaMean : ℕ → ℝ) (T : ℕ) {rho : ℝ}
    (hrhoIoo : rho ∈ Set.Ioo (0 : ℝ) 1)
    (hrhoEq :
      rhoLHS (hardWeight (proofDimension T))
          (hardTopWeight (proofDimension T)) rho =
        hardC (proofDimension T) ^ 2)
    (hzero : deltaMean 0 = initialDeficit (proofDimension T))
    (hstep : ∀ t < T,
      deltaMean t - deltaMean (t + 1) ≤
        8 * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)))
    (hfinal : deltaMean T = P.expect Delta)
    (hloss : ∀ omega,
      rho ^ 2 * hardC (proofDimension T) ^ 2 * Delta omega ^ 2 /
          (48 * (proofDimension T : ℝ) ^ 2) ≤ loss omega) :
    hardC (proofDimension T) ^ 2 /
        (768 * (proofDimension T : ℝ) ^ 2) ≤ P.expect loss := by
  have hmean0 := mean_deficit_from_oneQuery_steps deltaMean T hzero hstep
  have hmean : initialDeficit (proofDimension T) -
      8 * (T : ℝ) * (proofDimension T : ℝ) * (64 * (T + 1 : ℝ)) ≤
        P.expect Delta := by simpa [hfinal] using hmean0
  exact concrete_distributional_lower_bound_arithmetic P Delta loss T
    hrhoIoo hrhoEq hmean hloss

end Lemmata.DistributionalLowerBounds.Core.Distributional
