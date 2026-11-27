module

public import Lemmata.FrankWolfePS.Lower.Results

@[expose] public section

/-!
# Feasible methods

Suppose a method returns a feasible point on every instance. Its output is common to all
completions of a final transcript, and it is feasible on each of them. If one completion is
light (guessed mass at most `3/4`), the height argument on that completion forces the cost to
`1 / (8k)`, so the output has gap at least `1 / (16k)` on every completion. A transcript whose
untested set still has `127k` labels has a light completion.

The number of labels a run excludes is controlled by an exact potential: summed over the
completions, a run with `t` calls left makes at most `t C(|U|, h + 1)` fresh negative tests,
which is `31 t` per completion at the start. Hence at least `97/128 ≥ 3/4` of the instances fail
for each tape (the note's Appendix A has `5/7`).
-/

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
open scoped BigOperators

section Tree
variable {ι O : Type*} [DecidableEq ι]

/-- The fresh negative tests on the path of the hidden set `I`: tested labels of `U` (labels not
tested before) that are absent from `I`. -/
def Tree.exclusions {t} : Tree ι O t → Finset ι → Finset ι → ℕ
  | .leaf _, _, _ => 0
  | .pass s, I, U => s.exclusions I U
  | .probe i miss hit, I, U =>
      if i ∈ I then hit.exclusions I (U.erase i)
      else (if i ∈ U then 1 else 0) + miss.exclusions I (U.erase i)

/-- **The exclusion potential.** Summed over the completions `P ∪ S` of a transcript, a run with
`t` calls left makes at most `t C(|U|, h + 1)` fresh negative tests: a fresh test splits the
potential by Pascal's rule, a negative answer costs one exclusion and a positive one a call. -/
theorem exclusion_sum {t : ℕ} (s : Tree ι O t) (P U : Finset ι) (h : ℕ) (hPU : Disjoint P U) :
    ∑ S ∈ U.powersetCard h, s.exclusions (P ∪ S) U ≤ t * U.card.choose (h + 1) := by
  induction s generalizing P U h with
  | leaf x => simp [Tree.exclusions]
  | pass s ih =>
    simp only [Tree.exclusions]
    exact (ih P U h hPU).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  | @probe t i miss hit ihm ihy =>
    by_cases ip : i ∈ P
    · have iU : i ∉ U := disjoint_left.mp hPU ip
      have e : ∀ S ∈ U.powersetCard h, (Tree.probe i miss hit).exclusions (P ∪ S) U =
          hit.exclusions (P ∪ S) U := fun S _ => by
        simp [Tree.exclusions, ip, erase_eq_of_notMem iU]
      rw [sum_congr rfl e]
      exact (ihy P U h hPU).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
    by_cases iu : i ∈ U
    · set A := U.erase i with hA
      have hn : U.card = A.card + 1 := (card_erase_add_one iu).symm
      have hA' : Disjoint P A := hPU.mono_right (erase_subset _ _)
      have miss_eq (m : ℕ) : ∀ S ∈ A.powersetCard m,
          (Tree.probe i miss hit).exclusions (P ∪ S) U = 1 + miss.exclusions (P ∪ S) A :=
        fun S hs => by
          have hiS : i ∉ S := fun hi => (notMem_erase i U) ((mem_powersetCard.mp hs).1 hi)
          simp [Tree.exclusions, ip, hiS, iu, A]
      cases h with
      | zero =>
        have hm := ihm P A 0 hA'
        have e := miss_eq 0 ∅ (by simp)
        simp only [powersetCard_zero, sum_singleton, union_empty] at hm e ⊢
        rw [e, hn, Nat.choose_one_right]
        rw [Nat.choose_one_right] at hm
        nlinarith
      | succ j =>
        rw [sum_split U iu j]
        have hy := ihy (insert i P) A j (by simpa [A, disjoint_insert_left] using hA')
        have hm := ihm P A (j + 1) hA'
        have eqy : ∀ S ∈ A.powersetCard j,
            (Tree.probe i miss hit).exclusions (P ∪ insert i S) U =
              hit.exclusions (insert i P ∪ S) A := fun S _ => by
          have e : P ∪ insert i S = insert i P ∪ S := by
            ext b; simp only [mem_union, mem_insert]; tauto
          simp [Tree.exclusions, e, A]
        rw [← hA, sum_congr rfl (miss_eq (j + 1)), sum_congr rfl eqy, sum_add_distrib, sum_const,
          card_powersetCard, smul_eq_mul, mul_one, hn, Nat.choose_succ_succ' A.card (j + 1)]
        nlinarith
    · have e : ∀ S ∈ U.powersetCard h, (Tree.probe i miss hit).exclusions (P ∪ S) U =
          miss.exclusions (P ∪ S) U := fun S hs => by
        have hiS : i ∉ S := fun hi => iu ((mem_powersetCard.mp hs).1 hi)
        simp [Tree.exclusions, ip, hiS, iu]
      rw [sum_congr rfl e]
      exact ihm P U h hPU

end Tree

section Feasible
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A feasible run fails on a roomy path.** Suppose the run returns a feasible point for every
completion `P ∪ S` of the transcript. If the path of `P ∪ S` leaves at least `127 k` labels
untested (`127 k + t + X ≤ |U|`, where `X` counts its fresh negative tests), then the output on
`P ∪ S` has gap at least `1 / (16 k)`. -/
theorem feasible_path_failure {k t : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (s : Tree ι (Pt ι) t) (P U : Finset ι) (h : ℕ) (hPU : Disjoint P U)
    (calls : P.card + t ≤ k) (size : P.card + h = 8 * k)
    (feas : ∀ S ∈ U.powersetCard h, Feasible R (P ∪ S) (s.run (P ∪ S)))
    {S : Finset ι} (hS : S ∈ U.powersetCard h)
    (room : 127 * k + t + s.exclusions (P ∪ S) U ≤ U.card) :
    failure R k (P ∪ S) (s.run (P ∪ S)) := by
  induction s generalizing P U h S with
  | leaf x =>
    simp only [Tree.run] at feas ⊢
    simp only [Tree.exclusions, add_zero] at room
    obtain ⟨hSU, hSc⟩ := mem_powersetCard.mp hS
    have hhU : h ≤ U.card := hSc ▸ card_le_card hSU
    have small : 4 * ((P.card : ℝ) * U.card + (h : ℝ) ^ 2) ≤ 9 * k * U.card := by
      have b1 : (P.card : ℝ) ≤ k := by exact_mod_cast (by omega : P.card ≤ k)
      have b2 : (h : ℝ) ≤ 8 * k := by exact_mod_cast (by omega : h ≤ 8 * k)
      have b3 : 127 * (k : ℝ) ≤ U.card := by exact_mod_cast (by omega : 127 * k ≤ U.card)
      have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      have k0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    obtain ⟨S', hS', light⟩ := leaf_average hk x P U hPU (by omega) hhU small
    have hc' : (P ∪ S').card = 8 * k := by
      obtain ⟨sub, sz⟩ := mem_powersetCard.mp hS'
      rw [card_union_of_disjoint (hPU.mono_right sub), sz, size]
    have hc : (P ∪ S).card = 8 * k := by
      rw [card_union_of_disjoint (hPU.mono_right hSU), hSc, size]
    have cost := small_mass_objective hR hk hc' (feas S' hS') light
    right
    have hb := barycenter_upper hR hk hc
    have heq : 1 / (8 * (k : ℝ)) = 2 * (1 / (16 * (k : ℝ))) := by field_simp; ring
    linarith
  | pass s ih =>
    simp only [Tree.run, Tree.exclusions] at feas room ⊢
    exact ih P U h hPU (by omega) size feas hS (by omega)
  | @probe t i miss hit ihm ihy =>
    obtain ⟨hSU, hSc⟩ := mem_powersetCard.mp hS
    by_cases ip : i ∈ P
    · have iU : i ∉ U := disjoint_left.mp hPU ip
      have run (S' : Finset ι) : (Tree.probe i miss hit).run (P ∪ S') = hit.run (P ∪ S') := by
        simp [Tree.run, ip]
      have ex : (Tree.probe i miss hit).exclusions (P ∪ S) U = hit.exclusions (P ∪ S) U := by
        simp [Tree.exclusions, ip, erase_eq_of_notMem iU]
      rw [run]
      rw [ex] at room
      exact ihy P U h hPU (by omega) size (fun S' hS' => run S' ▸ feas S' hS') hS (by omega)
    by_cases iu : i ∈ U
    · set A := U.erase i with hA
      have hn : U.card = A.card + 1 := (card_erase_add_one iu).symm
      have hA' : Disjoint P A := hPU.mono_right (erase_subset _ _)
      by_cases iS : i ∈ S
      · have hpos : 0 < h := hSc ▸ card_pos.mpr ⟨i, iS⟩
        have hS'' : S.erase i ∈ A.powersetCard (h - 1) := by
          refine mem_powersetCard.mpr ⟨erase_subset_erase i hSU, ?_⟩
          rw [card_erase_of_mem iS, hSc]
        have e : P ∪ S = insert i P ∪ S.erase i := by
          ext b; by_cases hb : b = i
          · subst hb; simp [iS]
          · simp [hb]
        have hit_run (S' : Finset ι) :
            (Tree.probe i miss hit).run (insert i P ∪ S') = hit.run (insert i P ∪ S') := by
          simp [Tree.run]
        have ex : (Tree.probe i miss hit).exclusions (insert i P ∪ S.erase i) U =
            hit.exclusions (insert i P ∪ S.erase i) A := by
          simp [Tree.exclusions, A]
        rw [e, hit_run]
        rw [e, ex] at room
        have hPA : Disjoint (insert i P) A := by simpa [A, disjoint_insert_left] using hA'
        refine ihy (insert i P) A (h - 1) hPA (by rw [card_insert_of_notMem ip]; omega)
          (by rw [card_insert_of_notMem ip]; omega) (fun S' hS' => ?_) hS'' (by omega)
        have hiS' : i ∉ S' := fun hi => (notMem_erase i U) ((mem_powersetCard.mp hS').1 hi)
        have mem : insert i S' ∈ U.powersetCard h := by
          refine mem_powersetCard.mpr ⟨insert_subset iu
            (((mem_powersetCard.mp hS').1).trans (erase_subset _ _)), ?_⟩
          rw [card_insert_of_notMem hiS', (mem_powersetCard.mp hS').2]; omega
        have e' : P ∪ insert i S' = insert i P ∪ S' := by
          ext b; simp only [mem_union, mem_insert]; tauto
        have f := feas _ mem
        rw [e', hit_run] at f
        exact f
      · have hS' : S ∈ A.powersetCard h :=
          mem_powersetCard.mpr ⟨fun b hb => mem_erase.mpr ⟨fun e => iS (e ▸ hb), hSU hb⟩, hSc⟩
        have miss_run (S' : Finset ι) (hiS' : i ∉ S') :
            (Tree.probe i miss hit).run (P ∪ S') = miss.run (P ∪ S') := by
          simp [Tree.run, ip, hiS']
        have ex : (Tree.probe i miss hit).exclusions (P ∪ S) U =
            1 + miss.exclusions (P ∪ S) A := by
          simp [Tree.exclusions, ip, iS, iu, A]
        rw [miss_run S iS]
        rw [ex] at room
        refine ihm P A h hA' calls size (fun S' hS'' => ?_) hS' (by omega)
        have hiS' : i ∉ S' := fun hi => (notMem_erase i U) ((mem_powersetCard.mp hS'').1 hi)
        have mem : S' ∈ U.powersetCard h := mem_powersetCard.mpr
          ⟨((mem_powersetCard.mp hS'').1).trans (erase_subset _ _), (mem_powersetCard.mp hS'').2⟩
        have f := feas _ mem
        rw [miss_run S' hiS'] at f
        exact f
    · have miss_run (S' : Finset ι) (hS' : S' ∈ U.powersetCard h) :
          (Tree.probe i miss hit).run (P ∪ S') = miss.run (P ∪ S') := by
        have hiS' : i ∉ S' := fun hi => iu ((mem_powersetCard.mp hS').1 hi)
        simp [Tree.run, ip, hiS']
      have ex : (Tree.probe i miss hit).exclusions (P ∪ S) U = miss.exclusions (P ∪ S) U := by
        have hiS : i ∉ S := fun hi => iu (hSU hi)
        simp [Tree.exclusions, ip, hiS, iu]
      rw [miss_run S hS]
      rw [ex] at room
      exact ihm P U h hPU calls size (fun S' hS' => miss_run S' hS' ▸ feas S' hS') hS room

/-- **Feasible methods, fixed tape.** If a run returns a feasible point on every instance, at
least `97/128` of the instances have gap at least `1 / (16 k)`. -/
theorem feasible_fixed_tape (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {R : ℝ} (hR : 0 < R) (s : Orders ι (Pt ι) T)
    (feas : ∀ S ∈ shells T anchor, Feasible R (insert anchor S) (s.run (insert anchor S))) :
    (↑(shells T anchor).card : ℝ) * (97 / 128) ≤ ∑ S ∈ shells T anchor,
      flag (failure R (T + 1) (insert anchor S) (s.run (insert anchor S))) := by
  classical
  set k := T + 1 with hk_def
  have hk : 0 < k := Nat.succ_pos T
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set U := (univ : Finset ι).erase anchor with hU_def
  set h := 8 * k - 1 with hh_def
  have hn : U.card = 256 * k - 1 := by simp [U, hN, k]
  have hP : Disjoint ({anchor} : Finset ι) U := by simp [U]
  have hsh : shells T anchor = U.powersetCard h := rfl
  let tr := s.compile
  have run (S : Finset ι) : tr.run ({anchor} ∪ S) = s.run (insert anchor S) := by
    rw [singleton_union, Orders.run_compile]
  let X := fun S => tr.exclusions ({anchor} ∪ S) U
  have each (S : Finset ι) (hS : S ∈ shells T anchor) :
      1 - (X S : ℝ) / (128 * k) ≤
        flag (failure R k (insert anchor S) (s.run (insert anchor S))) := by
    by_cases few : X S ≤ 128 * k
    · have f := feasible_path_failure hk hR tr {anchor} U h hP (by simp; omega) (by simp; omega)
        (fun S' hS' => by rw [run]; exact feas S' hS') hS
        (by change 127 * k + T + X S ≤ U.card; omega)
      rw [run, singleton_union] at f
      have : (0 : ℝ) ≤ X S / (128 * k) := by positivity
      simp only [flag, f, ite_true]
      linarith
    · have hx : (128 * k : ℝ) < X S := by exact_mod_cast (by omega : 128 * k < X S)
      have : (1 : ℝ) < X S / (128 * k) := by rw [lt_div_iff₀ (by positivity)]; linarith
      linarith [flag_nonneg (failure R k (insert anchor S) (s.run (insert anchor S)))]
  have pot := exclusion_sum tr {anchor} U h hP
  have pascal : U.card.choose (h + 1) = 31 * U.card.choose h := by
    have c := Nat.choose_succ_right_eq U.card h
    have e1 : h + 1 = 8 * k := by omega
    have e2 : U.card - h = 31 * (8 * k) := by omega
    rw [e1, e2] at c
    rw [e1]
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 8 * k by omega)
    rw [c]; ring
  have potR : (∑ S ∈ shells T anchor, (X S : ℝ)) ≤ T * (31 * (U.card.choose h : ℝ)) := by
    rw [hsh]; exact_mod_cast (pascal ▸ pot)
  have hsc : ((shells T anchor).card : ℝ) = U.card.choose h := by
    rw [hsh, card_powersetCard]
  have sum_each := sum_le_sum each
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← sum_div] at sum_each
  rw [hsc] at sum_each ⊢
  have W0 : (0 : ℝ) ≤ U.card.choose h := Nat.cast_nonneg _
  have hT : (T : ℝ) + 1 = k := by simp [k]
  have frac : (∑ S ∈ shells T anchor, (X S : ℝ)) / (128 * k) ≤
      31 * (U.card.choose h : ℝ) / 128 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  change _ ≤ ∑ S ∈ shells T anchor, flag (failure R k (insert anchor S) (s.run (insert anchor S)))
  linarith

end Feasible

section Physical
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {Ω : Type*} [MeasurableSpace Ω]

/-- **Feasible methods on the hard family.** For a measurable randomized method requiring no more
than `T` calls that returns a feasible point on every instance, some instance, chosen before the
tape, has gap at least `L a² / (16 (T + 1))` with probability at least `3/4`, and expected gap at
least `3/4` of that. -/
theorem feasible_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Method (Ambient ι) T)
    (meas : ∀ S ∈ shells T anchor,
        Measurable (fun ω => (s ω).physicalRun a r anchor (insert anchor S)))
    (feas : ∀ S ∈ shells T anchor, ∀ ω,
      embed ((s ω).physicalRun a r anchor (insert anchor S)) ∈ physicalBody a r (insert anchor S)) :
    ∃ S ∈ shells T anchor, let I := insert anchor S
      (3 / 4 ≤ μ.real {ω | physicalFailure L a r (T + 1) I ((s ω).physicalRun a r anchor I)}) ∧
      3 / 4 * (L * a ^ 2 / (16 * ((T + 1 : ℕ) : ℝ))) ≤ ∫ ω,
          L * obj r ((s ω).physicalRun a r anchor I) - physicalOpt L a r I ∂μ := by
  classical
  have ne : (shells T anchor).Nonempty := by
    apply powersetCard_nonempty.mpr
    simp [hN]
    omega
  let e := fun S => {ω | physicalFailure L a r (T + 1) (insert anchor S)
    ((s ω).physicalRun a r anchor (insert anchor S))}
  have fixed (ω : Ω) :
      ((shells T anchor).card : ℝ) * (3 / 4) ≤ ∑ S ∈ shells T anchor, flag (ω ∈ e S) := by
    have conv (S : Finset ι) : ((((s ω).simulate a).orders (r / a) anchor).run (insert anchor S)) =
        scalePt a⁻¹ ((s ω).physicalRun a r anchor (insert anchor S)) := by
      rw [Method.orders_run, Method.simulate_run]
    have H := feasible_fixed_tape T anchor hN (div_pos hr ha)
      (((s ω).simulate a).orders (r / a) anchor)
      (fun S hS => by rw [conv]; exact (physical_feasible_iff ha hr _ _).mp (feas S hS ω))
    have c0 : (0 : ℝ) ≤ (shells T anchor).card := Nat.cast_nonneg _
    refine le_trans (by nlinarith) (H.trans (le_of_eq (sum_congr rfl fun S _ => ?_)))
    rw [conv]
    have iff := failure_scale hL ha hr (T + 1) (insert_nonempty anchor S)
      ((s ω).physicalRun a r anchor (insert anchor S))
    simp only [flag, e, Set.mem_ofPred_eq, iff]
  obtain ⟨S, hS, hp⟩ := select_tape _ ne μ (3 / 4) e
    (fun S hS => bad_measurable ha hr _ _ _ (meas S hS)) fixed
  exact ⟨S, hS, hp, expected_gap_of_fraction (T + 1) hL ha hr μ
    (insert_nonempty _ _) _ (meas S hS) (feas S hS) hp⟩

end Physical

end Lemmata.FrankWolfePS
