module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.PosteriorClosure

@[expose] public section

/-!
# Directed swap graph for one-query deficit drift

This module formalizes the regular directed graph and the exact edge-boundary
identity.  Query-specific separation bounds are developed on top of it.
-/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

/-- Swap two rank values in the image of a permutation. -/
def swapValues {m : ℕ} (sigma : Equiv.Perm (Fin m)) (a s : Fin m) :
    Equiv.Perm (Fin m) := sigma.trans (Equiv.swap a s)

@[simp] lemma swapValues_involutive {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (a s : Fin m) : swapValues (swapValues sigma a s) a s = sigma := by
  ext i
  simp [swapValues]

@[simp] lemma swapValues_apply {m : ℕ} (sigma : Equiv.Perm (Fin m))
    (a s i : Fin m) : swapValues sigma a s i = Equiv.swap a s (sigma i) := rfl

/-- A downward value swap stays on the Ferrers board. -/
lemma swapValues_compatible {m : ℕ} (D : FerrersData m)
    (sigma : FerrersPerm D) (row a : Fin m)
    (hlow : D.lower row ≤ a.val) (hlt : a < sigma.1 row) :
    ∀ k, D.lower k ≤ (swapValues sigma.1 a (sigma.1 row) k).val := by
  intro k
  let s := sigma.1 row
  change D.lower k ≤ ((Equiv.swap a s) (sigma.1 k)).val
  by_cases hka : sigma.1 k = a
  · rw [hka, Equiv.swap_apply_left]
    have hkold := sigma.2 k
    rw [hka] at hkold
    exact hkold.trans (Nat.le_of_lt hlt)
  · by_cases hks : sigma.1 k = s
    · have hkr : k = row := sigma.1.injective hks
      subst k
      rw [hks, Equiv.swap_apply_right]
      exact hlow
    · rw [Equiv.swap_apply_of_ne_of_ne hka hks]
      exact sigma.2 k

/-- One directed downward edge. -/
structure DownEdge {m : ℕ} (D : FerrersData m) where
  source : FerrersPerm D
  row : Fin m
  lowerValue : Fin m
  lower_allowed : D.lower row ≤ lowerValue.val
  lower_lt : lowerValue < source.1 row

namespace DownEdge

/-- Target of a downward edge. -/
noncomputable def target {m : ℕ} {D : FerrersData m} (e : DownEdge D) :
    FerrersPerm D :=
  ⟨swapValues e.source.1 e.lowerValue (e.source.1 e.row),
    swapValues_compatible D e.source e.row e.lowerValue e.lower_allowed e.lower_lt⟩

@[simp] lemma swap_target_back {m : ℕ} {D : FerrersData m}
    (e : DownEdge D) :
    swapValues e.target.1 e.lowerValue (e.source.1 e.row) = e.source.1 := by
  simp [target]

/-- Outgoing edges from one assignment. -/
def Outgoing {m : ℕ} (D : FerrersData m) (sigma : FerrersPerm D) :=
  {e : DownEdge D // e.source = sigma}

noncomputable instance fintypeDownEdge {m : ℕ} (D : FerrersData m) :
    Fintype (DownEdge D) :=
  Fintype.ofInjective
    (fun e : DownEdge D => (e.source, e.row, e.lowerValue)) (by
      intro e f h
      cases e
      cases f
      simp_all)

noncomputable instance {m : ℕ} (D : FerrersData m) (sigma : FerrersPerm D) :
    Fintype (Outgoing D sigma) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The deficit as a natural number. -/
def natDeficit {m : ℕ} (D : FerrersData m) : ℕ :=
  ∑ i, (D.choices i - 1)

lemma choices_sub_one {m : ℕ} (D : FerrersData m) (i : Fin m) :
    D.choices i - 1 = i.val - D.lower i := by
  unfold FerrersData.choices
  omega

lemma natDeficit_eq {m : ℕ} (D : FerrersData m) :
    natDeficit D = ∑ i, (i.val - D.lower i) := by
  unfold natDeficit
  apply Finset.sum_congr rfl
  intro i _
  exact choices_sub_one D i

/-- Number of admissible lower values for one row of one assignment. -/
lemma card_lowerValues {m : ℕ} (D : FerrersData m)
    (sigma : FerrersPerm D) (row : Fin m) :
    Fintype.card {a : Fin m // D.lower row ≤ a.val ∧ a < sigma.1 row} =
      (sigma.1 row).val - D.lower row := by
  let lo : Fin m := ⟨D.lower row,
    lt_of_le_of_lt (sigma.2 row) (sigma.1 row).isLt⟩
  have hset : {a : Fin m | D.lower row ≤ a.val ∧ a < sigma.1 row} =
      Set.Ico lo (sigma.1 row) := by
    ext a
    constructor
    · rintro ⟨ha, halt⟩
      exact ⟨by exact_mod_cast ha, halt⟩
    · rintro ⟨ha, halt⟩
      exact ⟨by exact_mod_cast ha, halt⟩
  rw [show Fintype.card {a : Fin m // D.lower row ≤ a.val ∧ a < sigma.1 row} =
      Fintype.card (Set.Ico lo (sigma.1 row)) by
    apply Fintype.card_congr
    exact Set.equivOfEq hset]
  simp [Fintype.card_Ico, Fin.card_Ico, lo]

/-- Outdegree is exactly the deficit, independently of the assignment. -/
theorem card_outgoing {m : ℕ} (D : FerrersData m) (sigma : FerrersPerm D) :
    Fintype.card (Outgoing D sigma) = natDeficit D := by
  -- An outgoing edge is a row together with one admissible lower value.
  let E : Outgoing D sigma ≃
      Σ row : Fin m, {a : Fin m // D.lower row ≤ a.val ∧ a < sigma.1 row} :=
    { toFun := fun e => ⟨e.1.row, ⟨e.1.lowerValue,
        e.1.lower_allowed, by simpa [e.2] using e.1.lower_lt⟩⟩
      invFun := fun ra => ⟨{
        source := sigma
        row := ra.1
        lowerValue := ra.2.1
        lower_allowed := ra.2.2.1
        lower_lt := ra.2.2.2 }, rfl⟩
      left_inv := by rintro ⟨e, rfl⟩; rfl
      right_inv := by rintro ⟨row, a, ha⟩; rfl }
  rw [Fintype.card_congr E, Fintype.card_sigma]
  simp_rw [card_lowerValues]
  rw [natDeficit_eq]
  have hsigmaSum : (∑ row, (sigma.1 row).val) = ∑ row : Fin m, row.val := by
    exact Equiv.sum_comp sigma.1 (fun row => row.val)
  have hleft : (∑ row, ((sigma.1 row).val - D.lower row)) +
      ∑ row, D.lower row = ∑ row, (sigma.1 row).val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro row _
    have hb := sigma.2 row
    omega
  have hright : (∑ row : Fin m, (row.val - D.lower row)) +
      ∑ row, D.lower row = ∑ row : Fin m, row.val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro row _
    have hb := D.feasible row
    omega
  omega

/-- Whether an edge is cut by an answer partition. -/
def IsCut {m : ℕ} {D : FerrersData m} {A : Type*}
    (answer : FerrersPerm D → A) (e : DownEdge D) : Prop :=
  answer e.source ≠ answer e.target

/-- Number of cut outgoing edges at a source. -/
noncomputable instance fintypeCut {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) (sigma : FerrersPerm D) :
    Fintype {e : Outgoing D sigma // IsCut answer e.1} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance fintypeInternal {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) (sigma : FerrersPerm D) :
    Fintype {e : Outgoing D sigma // ¬ IsCut answer e.1} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def cutOutdegree {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) (sigma : FerrersPerm D) : ℕ :=
  Fintype.card {e : Outgoing D sigma // IsCut answer e.1}

/-- Remaining internal outdegree at a source. -/
noncomputable def internalOutdegree {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) (sigma : FerrersPerm D) : ℕ :=
  Fintype.card {e : Outgoing D sigma // ¬ IsCut answer e.1}

lemma cut_add_internal {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) (sigma : FerrersPerm D) :
    cutOutdegree answer sigma + internalOutdegree answer sigma = natDeficit D := by
  rw [← card_outgoing D sigma]
  classical
  have hcomp := Fintype.card_subtype_compl
    (p := fun e : Outgoing D sigma => IsCut answer e.1)
  have hcutle : cutOutdegree answer sigma ≤ Fintype.card (Outgoing D sigma) :=
    Fintype.card_subtype_le _
  unfold cutOutdegree internalOutdegree at *
  omega

/-- Exact finite edge-boundary identity. -/
theorem edge_boundary_identity {m : ℕ} {D : FerrersData m}
    {A : Type*} [DecidableEq A]
    (answer : FerrersPerm D → A) :
    uniformAverage (fun sigma =>
      (natDeficit D : ℝ) - internalOutdegree answer sigma) =
      (∑ sigma, (cutOutdegree answer sigma : ℝ)) /
        Fintype.card (FerrersPerm D) := by
  unfold uniformAverage
  apply congrArg (fun x : ℝ => x / Fintype.card (FerrersPerm D))
  apply Finset.sum_congr rfl
  intro sigma _
  have hci := cut_add_internal answer sigma
  have hint : internalOutdegree answer sigma ≤ natDeficit D := by omega
  have hnat : natDeficit D - internalOutdegree answer sigma =
      cutOutdegree answer sigma := by omega
  change (natDeficit D : ℝ) - (internalOutdegree answer sigma : ℝ) =
    (cutOutdegree answer sigma : ℝ)
  rw [← Nat.cast_sub hint]
  exact_mod_cast hnat

end DownEdge

/-! ## Active-larger-rank switching injection -/

structure QueryRanks {m : ℕ} (D : FerrersData m) where
  rank : Fin m → ℕ
  rank_pos : ∀ i, 0 < rank i
  rank_strict : StrictMono rank
  q : Fin m → ℝ
  q_nonneg : ∀ i, 0 ≤ q i
  tau : FerrersPerm D → ℝ
  /-- Consequence of the water-level equation used by the switching proof. -/
  term_lt_one : ∀ sigma i k,
    (rank (sigma.1 i) : ℝ) < tau sigma * q i →
    ((rank (sigma.1 i) : ℝ) / q i) * q k - rank (sigma.1 k) < 1
  /-- Every individual raw term is below one before the root. -/
  below_term : ∀ sigma t k, t < tau sigma →
    t * q k - rank (sigma.1 k) < 1

namespace QueryRanks

/-- Build the query certificate directly from a monotone known contribution
and the water-level root equation. -/
noncomputable def ofWater {m : ℕ} {D : FerrersData m}
    (rank : Fin m → ℕ) (hrankPos : ∀ i, 0 < rank i)
    (hrankStrict : StrictMono rank)
    (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i)
    (known : ℝ → ℝ) (hknownMono : Monotone known)
    (hknownNonneg : ∀ t, 0 ≤ known t)
    (tau : FerrersPerm D → ℝ)
    (hroot : ∀ sigma,
      known (tau sigma) +
        ∑ k, max 0 (tau sigma * q k - rank (sigma.1 k)) = 1)
    (hbelow : ∀ sigma t, t < tau sigma →
      known t + ∑ k, max 0 (t * q k - rank (sigma.1 k)) < 1) :
    QueryRanks D where
  rank := rank
  rank_pos := hrankPos
  rank_strict := hrankStrict
  q := q
  q_nonneg := hq
  tau := tau
  term_lt_one := by
    intro sigma i k hactive
    have hrs : 0 < (rank (sigma.1 i) : ℝ) := by exact_mod_cast hrankPos _
    have hqi : 0 < q i := by
      by_contra hn
      have hz : q i = 0 := le_antisymm (le_of_not_gt hn) (hq i)
      rw [hz, mul_zero] at hactive
      linarith
    let t : ℝ := (rank (sigma.1 i) : ℝ) / q i
    have httau : t < tau sigma := by
      dsimp [t]
      exact (div_lt_iff₀ hqi).2 hactive
    have hknown : known t ≤ known (tau sigma) := hknownMono httau.le
    have hterms :
        (∑ j, max 0 (t * q j - rank (sigma.1 j))) <
          ∑ j, max 0 (tau sigma * q j - rank (sigma.1 j)) := by
      apply Finset.sum_lt_sum
      · intro j _
        apply max_le_max_left
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right httau.le (hq j)) _
      · refine ⟨i, Finset.mem_univ i, ?_⟩
        have htzero : t * q i - rank (sigma.1 i) = 0 := by
          dsimp [t]
          field_simp [hqi.ne']
          ring
        rw [htzero, max_eq_left (le_rfl)]
        rw [max_eq_right]
        · linarith
        · linarith
    have htotal : known t +
        (∑ j, max 0 (t * q j - rank (sigma.1 j))) < 1 := by
      rw [← hroot sigma]
      exact add_lt_add_of_le_of_lt hknown hterms
    have hkterm : t * q k - rank (sigma.1 k) < 1 := by
      have hmaxle : max 0 (t * q k - rank (sigma.1 k)) ≤
          ∑ j, max 0 (t * q j - rank (sigma.1 j)) :=
        Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
            le_max_left (0 : ℝ) (t * q j - rank (sigma.1 j)))
          (Finset.mem_univ k)
      have hbase0 := hknownNonneg t
      have hraw : t * q k - rank (sigma.1 k) ≤
          max 0 (t * q k - rank (sigma.1 k)) := le_max_right _ _
      linarith
    exact hkterm
  below_term := by
    intro sigma t k httau
    have htotal := hbelow sigma t httau
    have hmaxle : max 0 (t * q k - rank (sigma.1 k)) ≤
        ∑ j, max 0 (t * q j - rank (sigma.1 j)) :=
      Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
          le_max_left (0 : ℝ) (t * q j - rank (sigma.1 j)))
        (Finset.mem_univ k)
    have hraw : t * q k - rank (sigma.1 k) ≤
        max 0 (t * q k - rank (sigma.1 k)) := le_max_right _ _
    have hbase := hknownNonneg t
    linarith

/-- The larger-rank row of an edge is active. -/
def ActiveEdge {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :=
  {e : DownEdge D //
    (Q.rank (e.source.1 e.row) : ℝ) < Q.tau e.source * Q.q e.row}

noncomputable instance {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :
    Fintype (ActiveEdge Q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Switching map from active downward edges to `(target, larger rank)`. -/
noncomputable def activeSwitch {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : ActiveEdge Q) : FerrersPerm D × Fin m :=
  (e.1.target, e.1.source.1 e.1.row)

private lemma active_ratio {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) (e : ActiveEdge Q) (k : Fin m) :
    Q.q k / Q.q e.1.row <
      ((Q.rank (e.1.source.1 k) : ℝ) + 1) /
        Q.rank (e.1.source.1 e.1.row) := by
  have hqi : 0 < Q.q e.1.row := by
    have hrs : 0 < (Q.rank (e.1.source.1 e.1.row) : ℝ) := by
      exact_mod_cast Q.rank_pos _
    have ht := e.2
    have hq0 := Q.q_nonneg e.1.row
    by_contra h
    have : Q.q e.1.row = 0 := le_antisymm (le_of_not_gt h) hq0
    rw [this, mul_zero] at ht
    linarith
  have hrs : 0 < (Q.rank (e.1.source.1 e.1.row) : ℝ) := by
    exact_mod_cast Q.rank_pos _
  have ht := Q.term_lt_one e.1.source e.1.row k e.2
  apply (div_lt_div_iff₀ hqi hrs).2
  field_simp [hqi.ne'] at ht
  nlinarith

/-- The active switching map is injective. -/
theorem activeSwitch_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Function.Injective Q.activeSwitch := by
  intro e f hef
  have ht : e.1.target = f.1.target := congrArg Prod.fst hef
  have hs : e.1.source.1 e.1.row = f.1.source.1 f.1.row :=
    congrArg Prod.snd hef
  let s : Fin m := e.1.source.1 e.1.row
  have hfs : f.1.source.1 f.1.row = s := hs.symm
  by_cases hik : e.1.row = f.1.row
  · have ha : e.1.lowerValue = f.1.lowerValue := by
      have hv := DFunLike.congr_fun (congrArg Subtype.val ht) e.1.row
      simp only [DownEdge.target, swapValues_apply, Equiv.swap_apply_right] at hv
      simpa [hik] using hv
    have hsource : e.1.source = f.1.source := by
      apply Subtype.ext
      calc
        e.1.source.1 = swapValues e.1.target.1 e.1.lowerValue
            (e.1.source.1 e.1.row) := (DownEdge.swap_target_back e.1).symm
        _ = swapValues f.1.target.1 f.1.lowerValue
            (f.1.source.1 f.1.row) := by rw [ht, ha, hs]
        _ = f.1.source.1 := DownEdge.swap_target_back f.1
    apply Subtype.ext
    cases e with
    | mk ee hea =>
      cases f with
      | mk ff hfa =>
        cases ee
        cases ff
        simp_all
  · let T := e.1.target
    let ai : Fin m := e.1.lowerValue
    let ak : Fin m := f.1.lowerValue
    have hTi : T.1 e.1.row = ai := by
      simp [T, DownEdge.target, ai]
    have hTk : T.1 f.1.row = ak := by
      dsimp [T]
      rw [ht]
      simp [DownEdge.target, ak]
    have haik : ai ≠ ak := by
      intro h
      apply hik
      apply T.1.injective
      simp [hTi, hTk, h]
    have hais : ai ≠ s := ne_of_lt e.1.lower_lt
    have hak_s : ak < s := by
      simpa [ak, s, hfs] using f.1.lower_lt
    have haks : ak ≠ s := ne_of_lt hak_s
    have heAtK : e.1.source.1 f.1.row = ak := by
      have hv := hTk
      dsimp [T, DownEdge.target] at hv
      have hv' := congrArg (Equiv.swap ai s) hv
      have hfix : (Equiv.swap ai s) ak = ak :=
        Equiv.swap_apply_of_ne_of_ne haik.symm haks
      rw [hfix] at hv'
      simpa [ai, s] using hv'
    have hfAtI : f.1.source.1 e.1.row = ai := by
      have hv := hTi
      dsimp [T] at hv
      rw [ht] at hv
      dsimp [DownEdge.target] at hv
      rw [hfs] at hv
      have hv' := congrArg (Equiv.swap ak s) hv
      have hfix : (Equiv.swap ak s) ai = ai :=
        Equiv.swap_apply_of_ne_of_ne haik hais
      rw [hfix] at hv'
      simpa [ak, s] using hv'
    have hratio1 := active_ratio Q e f.1.row
    have hratio2 := active_ratio Q f e.1.row
    rw [heAtK] at hratio1
    rw [hfAtI, hfs] at hratio2
    change Q.q f.1.row / Q.q e.1.row <
      ((Q.rank ak : ℝ) + 1) / Q.rank s at hratio1
    change Q.q e.1.row / Q.q f.1.row <
      ((Q.rank ai : ℝ) + 1) / Q.rank s at hratio2
    have hqi : 0 < Q.q e.1.row := by
      have := e.2
      have hrs : 0 < (Q.rank s : ℝ) := by exact_mod_cast Q.rank_pos s
      have hq0 := Q.q_nonneg e.1.row
      by_contra h
      have hz : Q.q e.1.row = 0 := le_antisymm (le_of_not_gt h) hq0
      rw [hz, mul_zero] at this
      linarith
    have hqk : 0 < Q.q f.1.row := by
      have := f.2
      have hrs : 0 < (Q.rank s : ℝ) := by
        rw [← hfs]
        exact_mod_cast Q.rank_pos _
      have hq0 := Q.q_nonneg f.1.row
      by_contra h
      have hz : Q.q f.1.row = 0 := le_antisymm (le_of_not_gt h) hq0
      rw [hz, mul_zero] at this
      linarith
    have hrs : 0 < (Q.rank s : ℝ) := by exact_mod_cast Q.rank_pos s
    have hprod : (1 : ℝ) <
        (((Q.rank ak : ℝ) + 1) * ((Q.rank ai : ℝ) + 1)) /
          (Q.rank s : ℝ) ^ 2 := by
      have hm := mul_lt_mul_of_pos hratio1 hratio2
        (div_pos hqk hqi) (div_pos (by positivity) hrs)
      have hcancel : (Q.q f.1.row / Q.q e.1.row) *
          (Q.q e.1.row / Q.q f.1.row) = 1 := by
        field_simp [hqi.ne', hqk.ne']
      have hright :
          (((Q.rank ak : ℝ) + 1) / Q.rank s) *
              (((Q.rank ai : ℝ) + 1) / Q.rank s) =
            (((Q.rank ak : ℝ) + 1) * ((Q.rank ai : ℝ) + 1)) /
              (Q.rank s : ℝ) ^ 2 := by
        field_simp [hrs.ne']
      rw [hcancel, hright] at hm
      exact hm
    have hai_lt : Q.rank ai < Q.rank s := Q.rank_strict e.1.lower_lt
    have hak_lt : Q.rank ak < Q.rank s := Q.rank_strict hak_s
    have hdistinct : Q.rank ai ≠ Q.rank ak := Q.rank_strict.injective.ne haik
    have hnat : (Q.rank ak + 1) * (Q.rank ai + 1) ≤ Q.rank s ^ 2 := by
      rcases lt_or_gt_of_ne hdistinct with hia | hai
      · have h1 : Q.rank ai + 1 ≤ Q.rank ak := by omega
        have h2 : Q.rank ak + 1 ≤ Q.rank s := by omega
        calc
          (Q.rank ak + 1) * (Q.rank ai + 1) ≤
              (Q.rank ak + 1) * Q.rank ak :=
            Nat.mul_le_mul_left _ h1
          _ ≤ Q.rank s * Q.rank s := Nat.mul_le_mul h2 hak_lt.le
          _ = Q.rank s ^ 2 := by ring
      · have h1 : Q.rank ak + 1 ≤ Q.rank ai := by omega
        have h2 : Q.rank ai + 1 ≤ Q.rank s := by omega
        calc
          (Q.rank ak + 1) * (Q.rank ai + 1) ≤
              Q.rank ai * (Q.rank ai + 1) :=
            Nat.mul_le_mul_right _ h1
          _ ≤ Q.rank s * Q.rank s := Nat.mul_le_mul hai_lt.le h2
          _ = Q.rank s ^ 2 := by ring
    have hreal : ((Q.rank ak : ℝ) + 1) * ((Q.rank ai : ℝ) + 1) ≤
        (Q.rank s : ℝ) ^ 2 := by exact_mod_cast hnat
    have hden : 0 < (Q.rank s : ℝ) ^ 2 := by positivity
    have := (div_le_one hden).2 hreal
    linarith

/-- Cardinal version of the active-larger-rank bound. -/
theorem card_activeEdge_le {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) :
    Fintype.card (ActiveEdge Q) ≤ m * Fintype.card (FerrersPerm D) := by
  have hcard := Fintype.card_le_of_injective Q.activeSwitch
    (activeSwitch_injective Q)
  simpa [Fintype.card_prod, Nat.mul_comm] using hcard

/-! ## Query answer and cut-edge classification -/

/-- Full water-level data needed to compare the roots at two swap endpoints. -/
structure WaterQuery {m : ℕ} (D : FerrersData m) extends QueryRanks D where
  known : ℝ → ℝ
  known_nonneg : ∀ t, 0 ≤ known t
  root_eq : ∀ sigma,
    known (toQueryRanks.tau sigma) +
      ∑ k, max 0 (toQueryRanks.tau sigma * toQueryRanks.q k -
        toQueryRanks.rank (sigma.1 k)) = 1
  tau_le_of_profile_le : ∀ sigma t,
    known t + ∑ k, max 0 (t * toQueryRanks.q k -
      toQueryRanks.rank (sigma.1 k)) ≤ 1 → t ≤ toQueryRanks.tau sigma

namespace WaterQuery

/-- Package a concrete water-level profile into the query specification used by
the drift theorem. -/
noncomputable def ofWater {m : ℕ} {D : FerrersData m}
    (rank : Fin m → ℕ) (hrankPos : ∀ i, 0 < rank i)
    (hrankStrict : StrictMono rank)
    (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i)
    (known : ℝ → ℝ) (hknownMono : Monotone known)
    (hknownNonneg : ∀ t, 0 ≤ known t)
    (tau : FerrersPerm D → ℝ)
    (hroot : ∀ sigma,
      known (tau sigma) + ∑ k, max 0 (tau sigma * q k - rank (sigma.1 k)) = 1)
    (hbelow : ∀ sigma t, t < tau sigma →
      known t + ∑ k, max 0 (t * q k - rank (sigma.1 k)) < 1)
    (htauLe : ∀ sigma t,
      known t + ∑ k, max 0 (t * q k - rank (sigma.1 k)) ≤ 1 → t ≤ tau sigma) :
    WaterQuery D where
  toQueryRanks := QueryRanks.ofWater rank hrankPos hrankStrict q hq known
    hknownMono hknownNonneg tau hroot hbelow
  known := known
  known_nonneg := hknownNonneg
  root_eq := hroot
  tau_le_of_profile_le := htauLe

/-- Discrete answer information plus the recoverable real water level. -/
structure Answer (m : ℕ) where
  tau : ℝ
  activeRank : Fin m → Option (Fin m)
  inactiveLower : Fin m → ℕ

lemma Answer.eq_of_fields {m : ℕ} {a b : Answer m}
    (ht : a.tau = b.tau)
    (ha : a.activeRank = b.activeRank)
    (hl : a.inactiveLower = b.inactiveLower) : a = b := by
  cases a
  cases b
  simp_all

noncomputable def answer {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (sigma : FerrersPerm D) : Answer m where
  tau := W.toQueryRanks.tau sigma
  activeRank i := if (W.toQueryRanks.rank (sigma.1 i) : ℝ) <
      W.toQueryRanks.tau sigma * W.toQueryRanks.q i then some (sigma.1 i) else none
  inactiveLower i := Nat.ceil (W.toQueryRanks.tau sigma * W.toQueryRanks.q i)

/-- Row carrying the lower value at the source. -/
def lowerRow {m : ℕ} {D : FerrersData m} (e : DownEdge D) : Fin m :=
  e.source.1.symm e.lowerValue

@[simp] lemma source_lowerRow {m : ℕ} {D : FerrersData m} (e : DownEdge D) :
    e.source.1 (lowerRow e) = e.lowerValue := e.source.1.apply_symm_apply _

/-- Reverse orientation of a downward edge. -/
noncomputable def reverseEdge {m : ℕ} {D : FerrersData m} (e : DownEdge D) :
    DownEdge D where
  source := e.target
  row := lowerRow e
  lowerValue := e.lowerValue
  lower_allowed := by
    have := e.source.2 (lowerRow e)
    simpa using this
  lower_lt := by
    simp [DownEdge.target, lowerRow]
    exact e.lower_lt

@[simp] lemma reverseEdge_source {m : ℕ} {D : FerrersData m} (e : DownEdge D) :
    (reverseEdge e).source = e.target := rfl

@[simp] lemma reverseEdge_involutive {m : ℕ} {D : FerrersData m}
    (e : DownEdge D) : reverseEdge (reverseEdge e) = e := by
  cases e with
  | mk source row a hallowed hlt =>
    have hrow : (swapValues source.1 a (source.1 row)).symm a = row := by
      rw [Equiv.symm_apply_eq]
      simp [swapValues]
    simp [reverseEdge, lowerRow, DownEdge.target, hrow]
    rfl

@[simp] lemma reverseEdge_high {m : ℕ} {D : FerrersData m} (e : DownEdge D) :
    (reverseEdge e).source.1 (reverseEdge e).row = e.source.1 e.row := by
  simp [reverseEdge, DownEdge.target, lowerRow]

private lemma profile_swap_le {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : DownEdge D) {t : ℝ}
    (hhigh : t * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank (e.source.1 e.row))
    (hlow : t * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank e.lowerValue) :
    W.known t + ∑ k, max 0 (t * W.toQueryRanks.q k -
        W.toQueryRanks.rank (e.target.1 k)) ≤
      W.known t + ∑ k, max 0 (t * W.toQueryRanks.q k -
        W.toQueryRanks.rank (e.source.1 k)) := by
  apply add_le_add_right
  have hrowlow : lowerRow e ≠ e.row := by
    intro h
    have hv := source_lowerRow e
    rw [h] at hv
    exact (ne_of_lt e.lower_lt) hv.symm
  apply Finset.sum_le_sum
  intro k _
  by_cases hki : k = e.row
  · subst k
    have htgt : e.target.1 e.row = e.lowerValue := by
      simp [DownEdge.target]
    rw [htgt]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  · by_cases hkj : k = lowerRow e
    · subst k
      have hsrc := source_lowerRow e
      have htgt : e.target.1 (lowerRow e) = e.source.1 e.row := by
        simp [DownEdge.target, lowerRow]
      rw [hsrc, htgt]
      apply max_le_max_left
      have hrs := W.toQueryRanks.rank_strict e.lower_lt
      have hrsR : (W.toQueryRanks.rank e.lowerValue : ℝ) ≤
          (W.toQueryRanks.rank (e.source.1 e.row) : ℝ) :=
        Nat.cast_le.mpr hrs.le
      linarith
    · have hneA : e.source.1 k ≠ e.lowerValue := by
        intro h
        apply hkj
        exact e.source.1.injective (h.trans (source_lowerRow e).symm)
      have hneS : e.source.1 k ≠ e.source.1 e.row := by
        intro h
        exact hki (e.source.1.injective h)
      simp [DownEdge.target, Equiv.swap_apply_of_ne_of_ne hneA hneS]

/-- If neither endpoint is active or certifies the lower cell, the two water
levels coincide. -/
lemma tau_eq_of_inactive_uncertified {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : DownEdge D)
    (hsrcInactive : W.toQueryRanks.tau e.source * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank (e.source.1 e.row))
    (hsrcNoCert : W.toQueryRanks.tau e.source * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank e.lowerValue)
    (htgtInactive : W.toQueryRanks.tau e.target *
        W.toQueryRanks.q (reverseEdge e).row ≤
      W.toQueryRanks.rank (e.source.1 e.row))
    (htgtNoCert : W.toQueryRanks.tau e.target *
        W.toQueryRanks.q (reverseEdge e).row ≤
      W.toQueryRanks.rank e.lowerValue) :
    W.toQueryRanks.tau e.source = W.toQueryRanks.tau e.target := by
  have hprof1 := profile_swap_le W e hsrcInactive hsrcNoCert
  rw [W.root_eq e.source] at hprof1
  have hle1 := W.tau_le_of_profile_le e.target _ hprof1
  have htgtInactive' : W.toQueryRanks.tau e.target *
      W.toQueryRanks.q (reverseEdge e).row ≤
        W.toQueryRanks.rank ((reverseEdge e).source.1 (reverseEdge e).row) := by
    rw [reverseEdge_high]
    exact htgtInactive
  have hprof2 := profile_swap_le W (reverseEdge e) htgtInactive' htgtNoCert
  have hback : (reverseEdge e).target = e.source := by
    apply Subtype.ext
    simp [reverseEdge, DownEdge.target, lowerRow]
  rw [reverseEdge_source, hback, W.root_eq e.target] at hprof2
  have hle2 := W.tau_le_of_profile_le e.source _ hprof2
  exact le_antisymm hle1 hle2

/-- Under the same hypotheses, numerical answers coincide. -/
theorem answer_eq_of_inactive_uncertified {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : DownEdge D)
    (hsrcInactive : W.toQueryRanks.tau e.source * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank (e.source.1 e.row))
    (hsrcNoCert : W.toQueryRanks.tau e.source * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank e.lowerValue)
    (htgtInactive : W.toQueryRanks.tau e.target *
        W.toQueryRanks.q (reverseEdge e).row ≤
      W.toQueryRanks.rank (e.source.1 e.row))
    (htgtNoCert : W.toQueryRanks.tau e.target *
        W.toQueryRanks.q (reverseEdge e).row ≤
      W.toQueryRanks.rank e.lowerValue) :
    W.answer e.source = W.answer e.target := by
  have htau := W.tau_eq_of_inactive_uncertified e hsrcInactive hsrcNoCert
    htgtInactive htgtNoCert
  have hsrcInactiveT : W.toQueryRanks.tau e.target * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank (e.source.1 e.row) := by
    rw [← htau]
    exact hsrcInactive
  have hsrcNoCertT : W.toQueryRanks.tau e.target * W.toQueryRanks.q e.row ≤
      W.toQueryRanks.rank e.lowerValue := by
    rw [← htau]
    exact hsrcNoCert
  cases e with
  | mk source row a hallowed hlt =>
    have htau' : W.tau source =
        W.tau ⟨swapValues source.1 a (source.1 row),
          swapValues_compatible D source row a hallowed hlt⟩ := by
      simpa [DownEdge.target] using htau
    apply Answer.eq_of_fields htau'
    · funext k
      simp only [answer]
      rw [htau']
      by_cases hkrow : k = row
      · subst k
        have hsI : ¬(W.rank (source.1 row) : ℝ) <
            W.tau ⟨swapValues source.1 a (source.1 row),
              swapValues_compatible D source row a hallowed hlt⟩ * W.q row :=
          not_lt_of_ge (by simpa [DownEdge.target] using hsrcInactiveT)
        have haI : ¬(W.rank a : ℝ) <
            W.tau ⟨swapValues source.1 a (source.1 row),
              swapValues_compatible D source row a hallowed hlt⟩ * W.q row :=
          not_lt_of_ge (by simpa [DownEdge.target] using hsrcNoCertT)
        simp [DownEdge.target, hsI, haI]
      · by_cases hklow : k = (source.1.symm a)
        · subst k
          have haI : ¬(W.rank a : ℝ) <
              W.tau ⟨swapValues source.1 a (source.1 row),
                swapValues_compatible D source row a hallowed hlt⟩ *
                W.q (source.1.symm a) := not_lt_of_ge htgtNoCert
          have hsI : ¬(W.rank (source.1 row) : ℝ) <
              W.tau ⟨swapValues source.1 a (source.1 row),
                swapValues_compatible D source row a hallowed hlt⟩ *
                W.q (source.1.symm a) := not_lt_of_ge htgtInactive
          simp [DownEdge.target, haI, hsI]
        · have hneA : source.1 k ≠ a := by
            intro h
            apply hklow
            exact source.1.injective (h.trans (source.1.apply_symm_apply a).symm)
          have hneS : source.1 k ≠ source.1 row := by
            intro h
            exact hkrow (source.1.injective h)
          have hsame : (swapValues source.1 a (source.1 row)) k = source.1 k := by
            exact Equiv.swap_apply_of_ne_of_ne hneA hneS
          simp [DownEdge.target, hsame]
    · funext k
      simp only [answer]
      rw [htau']
      congr 2

/-- Every answer-cut edge is active at an endpoint or certified at an endpoint. -/
theorem cut_edge_classification {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : DownEdge D)
    (hcut : W.answer e.source ≠ W.answer e.target) :
    ((W.rank (e.source.1 e.row) : ℝ) < W.tau e.source * W.q e.row) ∨
    ((W.rank (e.source.1 e.row) : ℝ) <
      W.tau e.target * W.q (reverseEdge e).row) ∨
    (W.tau e.source * W.q e.row ≤ W.rank (e.source.1 e.row) ∧
      (W.rank e.lowerValue : ℝ) < W.tau e.source * W.q e.row) ∨
    (W.tau e.target * W.q (reverseEdge e).row ≤
        W.rank (e.source.1 e.row) ∧
      (W.rank e.lowerValue : ℝ) <
        W.tau e.target * W.q (reverseEdge e).row) := by
  by_contra h
  push Not at h
  rcases h with ⟨hsrcInactive, htgtInactive, hsrcNoCert, htgtNoCert⟩
  apply hcut
  exact W.answer_eq_of_inactive_uncertified e hsrcInactive
    (hsrcNoCert hsrcInactive) htgtInactive (htgtNoCert htgtInactive)

end WaterQuery

/-! ## Certified cells and the corrected direct record map -/

/-- An inactive larger-rank row whose zero answer excludes a lower value. -/
def CertifiedCell {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :=
  {e : DownEdge D //
    Q.tau e.source * Q.q e.row ≤ Q.rank (e.source.1 e.row) ∧
      (Q.rank e.lowerValue : ℝ) < Q.tau e.source * Q.q e.row}

noncomputable instance {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Fintype (CertifiedCell Q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- A row/value pair preceding all rows carrying smaller values in decreasing
query-magnitude order. -/
def RecordCell {m : ℕ} {D : FerrersData m} (Q : QueryRanks D) :=
  {x : FerrersPerm D × Fin m × Fin m //
    D.lower x.2.1 ≤ x.2.2.val ∧
      ∀ k, x.1.1 k < x.2.2 → Q.q k < Q.q x.2.1}

noncomputable instance {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) : Fintype (RecordCell Q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- A certified cell is already a record in the same assignment; no rank swap
is needed.  This corrects the non-injective swap map in the informal draft. -/
noncomputable def certifiedToRecord {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D)
    (c : CertifiedCell Q) : RecordCell Q :=
  ⟨(c.1.source, c.1.row, c.1.lowerValue), c.1.lower_allowed, by
    intro k hk
    have hranklt : Q.rank (c.1.source.1 k) < Q.rank c.1.lowerValue :=
      Q.rank_strict hk
    have hqi : 0 < Q.q c.1.row := by
      have hcert := c.2.2
      have hra : 0 < (Q.rank c.1.lowerValue : ℝ) := by
        exact_mod_cast Q.rank_pos _
      have hq0 := Q.q_nonneg c.1.row
      by_contra hn
      have hz : Q.q c.1.row = 0 := le_antisymm (le_of_not_gt hn) hq0
      rw [hz, mul_zero] at hcert
      linarith
    let t : ℝ := (Q.rank c.1.lowerValue : ℝ) / Q.q c.1.row
    have httau : t < Q.tau c.1.source := by
      dsimp [t]
      exact (div_lt_iff₀ hqi).2 c.2.2
    have hterm := Q.below_term c.1.source t k httau
    by_contra hqki
    have hqle : Q.q c.1.row ≤ Q.q k := le_of_not_gt hqki
    have hgapNat : Q.rank (c.1.source.1 k) + 1 ≤
        Q.rank c.1.lowerValue := by omega
    have hgapReal : (Q.rank (c.1.source.1 k) : ℝ) + 1 ≤
        Q.rank c.1.lowerValue := by exact_mod_cast hgapNat
    have hrankgap : (1 : ℝ) ≤
        (Q.rank c.1.lowerValue : ℝ) - Q.rank (c.1.source.1 k) := by
      linarith
    have hmul : (Q.rank c.1.lowerValue : ℝ) ≤ t * Q.q k := by
      dsimp [t]
      have := mul_le_mul_of_nonneg_left hqle
        (show 0 ≤ (Q.rank c.1.lowerValue : ℝ) / Q.q c.1.row by positivity)
      field_simp [hqi.ne'] at this ⊢
      nlinarith
    linarith⟩

lemma certifiedToRecord_injective {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) :
    Function.Injective Q.certifiedToRecord := by
  intro c e h
  have hv := congrArg Subtype.val h
  have hs : c.1.source = e.1.source := congrArg (fun x => x.1) hv
  have hr : c.1.row = e.1.row := congrArg (fun x => x.2.1) hv
  have hl : c.1.lowerValue = e.1.lowerValue := congrArg (fun x => x.2.2) hv
  apply Subtype.ext
  cases c with
  | mk c hc =>
    cases e with
    | mk e he =>
      cases c
      cases e
      simp_all

/-- Edges cut by the exact water-level answer. -/
def WaterCutEdge {m : ℕ} {D : FerrersData m} (W : WaterQuery D) :=
  {e : DownEdge D // W.answer e.source ≠ W.answer e.target}

noncomputable instance {m : ℕ} {D : FerrersData m} (W : WaterQuery D) :
    Fintype (WaterCutEdge W) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Four tagged charge classes: active at source/target and certified at
source/target. -/
abbrev EdgeCharge {m : ℕ} {D : FerrersData m} (W : WaterQuery D) :=
  ActiveEdge W.toQueryRanks ⊕ ActiveEdge W.toQueryRanks ⊕
    CertifiedCell W.toQueryRanks ⊕ CertifiedCell W.toQueryRanks

noncomputable def chargeCutEdge {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : WaterCutEdge W) : EdgeCharge W := by
  classical
  let E := e.1
  by_cases hsrcA : (W.rank (E.source.1 E.row) : ℝ) < W.tau E.source * W.q E.row
  · exact Sum.inl ⟨E, hsrcA⟩
  by_cases htgtA : (W.rank (E.source.1 E.row) : ℝ) <
      W.tau E.target * W.q (WaterQuery.reverseEdge E).row
  · exact Sum.inr (Sum.inl ⟨WaterQuery.reverseEdge E, by
      rw [WaterQuery.reverseEdge_high]
      exact htgtA⟩)
  by_cases hsrcC : W.tau E.source * W.q E.row ≤ W.rank (E.source.1 E.row) ∧
      (W.rank E.lowerValue : ℝ) < W.tau E.source * W.q E.row
  · exact Sum.inr (Sum.inr (Sum.inl ⟨E, hsrcC⟩))
  · have hlast : W.tau E.target * W.q (WaterQuery.reverseEdge E).row ≤
        W.rank (E.source.1 E.row) ∧
      (W.rank E.lowerValue : ℝ) <
        W.tau E.target * W.q (WaterQuery.reverseEdge E).row := by
      have hall := W.cut_edge_classification E e.2
      rcases hall with h | h | h | h
      · exact (hsrcA h).elim
      · exact (htgtA h).elim
      · exact (hsrcC h).elim
      · exact h
    exact Sum.inr (Sum.inr (Sum.inr
      ⟨WaterQuery.reverseEdge E, by
        constructor
        · rw [WaterQuery.reverseEdge_high]
          exact hlast.1
        · exact hlast.2⟩))

noncomputable def unchargeEdge {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) : EdgeCharge W → DownEdge D
  | Sum.inl e => e.1
  | Sum.inr (Sum.inl e) => WaterQuery.reverseEdge e.1
  | Sum.inr (Sum.inr (Sum.inl e)) => e.1
  | Sum.inr (Sum.inr (Sum.inr e)) => WaterQuery.reverseEdge e.1

lemma uncharge_chargeCutEdge {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) (e : WaterCutEdge W) :
    unchargeEdge W (chargeCutEdge W e) = e.1 := by
  classical
  unfold chargeCutEdge
  dsimp
  split_ifs <;> simp [unchargeEdge]

lemma chargeCutEdge_injective {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) : Function.Injective (chargeCutEdge W) := by
  intro e f h
  apply Subtype.ext
  calc
    e.1 = unchargeEdge W (chargeCutEdge W e) := (uncharge_chargeCutEdge W e).symm
    _ = unchargeEdge W (chargeCutEdge W f) := congrArg (unchargeEdge W) h
    _ = f.1 := uncharge_chargeCutEdge W f

/-- Certified-cell cardinality is bounded by the record proxy. -/
theorem card_certified_le_record {m : ℕ} {D : FerrersData m}
    (Q : QueryRanks D) :
    Fintype.card (CertifiedCell Q) ≤ Fintype.card (RecordCell Q) :=
  Fintype.card_le_of_injective Q.certifiedToRecord
    (certifiedToRecord_injective Q)

/-- Cardinal form of the active/certified cut-edge reduction. -/
theorem card_waterCutEdge_le {m : ℕ} {D : FerrersData m}
    (W : WaterQuery D) :
    Fintype.card (WaterCutEdge W) ≤
      2 * m * Fintype.card (FerrersPerm D) +
        2 * Fintype.card (RecordCell W.toQueryRanks) := by
  have hcharge := Fintype.card_le_of_injective (chargeCutEdge W)
    (chargeCutEdge_injective W)
  simp only [EdgeCharge, Fintype.card_sum] at hcharge
  have hcharge' : Fintype.card (WaterCutEdge W) ≤
      2 * Fintype.card (ActiveEdge W.toQueryRanks) +
        2 * Fintype.card (CertifiedCell W.toQueryRanks) := by omega
  have hactive := card_activeEdge_le W.toQueryRanks
  have hcert := card_certified_le_record W.toQueryRanks
  have hsum := Nat.add_le_add (Nat.mul_le_mul_left 2 hactive)
    (Nat.mul_le_mul_left 2 hcert)
  exact hcharge'.trans (by simpa [Nat.mul_assoc] using hsum)

end QueryRanks
end Lemmata.DistributionalLowerBounds.Core.Distributional
