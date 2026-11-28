module

public import Lemmata.OracleComplexity.Deviation

@[expose] public section

/-!
# Emulation of the oracle of Section IV.B

A label `(i, k)` stands for bit `k` of coordinate `i`; its value is the value of coordinate `i` if
its string first leaves the greedy path at bit `k`. The query guesses the bits of all greedy paths,
ordered by the confidence order: larger values first, then smaller coordinates, then smaller bits.
Since the values decrease along each path, the bits of one coordinate are asked in order. If the
first wrong guess is at the label `(i, k)`, then the string of coordinate `i` leaves its path at
`k`, every label before it was guessed right, and every other coordinate either follows its path
throughout or has value at most that of its first label after `(i, k)`, which comes later in the
confidence order. The answer completes every string accordingly; the completed strings have the
same value, least active coordinate and slope (`cube_oracle_congr`).
-/

namespace Lemmata.OracleComplexity

variable {n M : ℕ} [NeZero n]

/-- Two instances get the same oracle answer if they agree on a coordinate `i₀`, and every other
coordinate is either the same or dominated: its value under `S` is at most its value under `T`,
which is below the value of `i₀`, or equal to it with a larger index. -/
theorem cube_oracle_congr {S T : Fin n → Fin M → Bool} {x : Fin n → ℝ} (i₀ : Fin n)
    (hval : boxFn (S i₀) (x i₀) = boxFn (T i₀) (x i₀))
    (horc : boxOracle (S i₀) (x i₀) = boxOracle (T i₀) (x i₀))
    (hother : ∀ j, j ≠ i₀ → S j = T j ∨ (boxFn (S j) (x j) ≤ boxFn (T j) (x j) ∧
      (boxFn (T j) (x j) < boxFn (T i₀) (x i₀) ∨
        (boxFn (T j) (x j) = boxFn (T i₀) (x i₀) ∧ i₀ < j)))) :
    cubeOracle S x = cubeOracle T x := by
  have hdom : ∀ j, j ≠ i₀ → S j ≠ T j → boxFn (S j) (x j) ≤ boxFn (T j) (x j) ∧
      boxFn (T j) (x j) ≤ boxFn (T i₀) (x i₀) ∧
      (boxFn (T j) (x j) = boxFn (T i₀) (x i₀) → i₀ < j) := by
    intro j hj hne
    rcases hother j hj with h | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact absurd h hne
    · exact ⟨h1, h2.le, fun h => absurd h h2.ne⟩
    · exact ⟨h1, h2.le, fun _ => h3⟩
  have hV : cubeFn S x = cubeFn T x := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      by_cases hj : j = i₀
      · subst hj; rw [hval]; exact coord_le_cube T x _
      · by_cases he : S j = T j
        · rw [he]; exact coord_le_cube T x j
        · exact (hdom j hj he).1.trans (coord_le_cube T x j)
    · apply Finset.sup'_le
      intro j _
      by_cases hj : j = i₀
      · subst hj; rw [← hval]; exact coord_le_cube S x _
      · by_cases he : S j = T j
        · rw [← he]; exact coord_le_cube S x j
        · exact (hdom j hj he).2.1.trans (hval ▸ coord_le_cube S x i₀)
  -- the least active coordinates agree
  have hS₀ : boxFn (S i₀) (x i₀) ≤ cubeFn S x := coord_le_cube S x i₀
  have hT₀ : boxFn (T i₀) (x i₀) ≤ cubeFn T x := coord_le_cube T x i₀
  obtain ⟨hcS, hminS⟩ := cubeCoord_spec S x
  obtain ⟨hcT, hminT⟩ := cubeCoord_spec T x
  have hnotdomS : cubeCoord S x = i₀ ∨ S (cubeCoord S x) = T (cubeCoord S x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hdom _ hcon.1 hcon.2
    have heq : boxFn (T (cubeCoord S x)) (x (cubeCoord S x)) = boxFn (T i₀) (x i₀) := by
      apply le_antisymm h2
      rw [← hval]; linarith
    have hlt := h3 heq
    have hi₀ : boxFn (S i₀) (x i₀) = cubeFn S x := by
      apply le_antisymm hS₀
      rw [hval, ← heq]; linarith
    exact absurd (hminS i₀ hi₀) (not_le.mpr hlt)
  have hnotdomT : cubeCoord T x = i₀ ∨ S (cubeCoord T x) = T (cubeCoord T x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hdom _ hcon.1 hcon.2
    have heq : boxFn (T (cubeCoord T x)) (x (cubeCoord T x)) = boxFn (T i₀) (x i₀) := by
      apply le_antisymm h2
      rw [hcT]; exact hT₀
    have hlt := h3 heq
    have hi₀ : boxFn (T i₀) (x i₀) = cubeFn T x := by
      apply le_antisymm hT₀
      rw [← heq, hcT]
    exact absurd (hminT i₀ hi₀) (not_le.mpr hlt)
  have hactT : boxFn (T (cubeCoord S x)) (x (cubeCoord S x)) = cubeFn T x := by
    rcases hnotdomS with h | h
    · rw [h, ← hval, ← hV]; rw [h] at hcS; exact hcS
    · rw [← h, ← hV]; exact hcS
  have hactS : boxFn (S (cubeCoord T x)) (x (cubeCoord T x)) = cubeFn S x := by
    rcases hnotdomT with h | h
    · rw [h, hval, hV]; rw [h] at hcT; exact hcT
    · rw [h, hV]; exact hcT
  have hc : cubeCoord S x = cubeCoord T x :=
    le_antisymm (hminS _ hactS) (hminT _ hactT)
  have hslope : (boxOracle (S (cubeCoord S x)) (x (cubeCoord S x))).2 =
      (boxOracle (T (cubeCoord S x)) (x (cubeCoord S x))).2 := by
    rcases hnotdomS with h | h
    · rw [h, horc]
    · rw [h]
  unfold cubeOracle
  rw [hV, ← hc, hslope]

/-- The confidence order on labels: larger deviation values first, then smaller coordinates, then
smaller bits. -/
noncomputable def labKey (x : Fin n → ℝ) (a : Fin n × Fin M) : Lex (ℝᵒᵈ × Lex (Fin n × Fin M)) :=
  toLex (OrderDual.toDual (devVal M (x a.1) a.2), toLex a)

omit [NeZero n] in
theorem labKey_inj (x : Fin n → ℝ) {a b : Fin n × Fin M} (h : labKey x a = labKey x b) :
    a = b := by
  unfold labKey at h
  have := congrArg (fun p => (ofLex p).2) h
  simpa using this

omit [NeZero n] in
theorem labKey_lt_iff (x : Fin n → ℝ) (a b : Fin n × Fin M) :
    labKey x a < labKey x b ↔ devVal M (x b.1) b.2 < devVal M (x a.1) a.2 ∨
      (devVal M (x a.1) a.2 = devVal M (x b.1) b.2 ∧
        (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))) := by
  unfold labKey
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  simp only [OrderDual.toDual_lt_toDual, OrderDual.toDual_inj]

open Classical in
/-- The labels in the confidence order. -/
noncomputable def cubeLabels (x : Fin n → ℝ) : List (Fin n × Fin M) :=
  List.mergeSort (List.finRange n ×ˢ List.finRange M) (fun a b => decide (labKey x a ≤ labKey x b))

/-- The query: guess the bits of the greedy paths, in the confidence order. -/
noncomputable def cubeQuery (x : Fin n → ℝ) : List (Fin (n * M) × Bool) :=
  (cubeLabels x).map (fun a => (finProdFinEquiv a, pathBit (x a.1) a.2))

open Classical in
/-- The first bit of coordinate `j` whose label does not come before `a` (or `M`). -/
noncomputable def firstOut (x : Fin n → ℝ) (a : Fin n × Fin M) (j : Fin n) : ℕ :=
  Nat.find (⟨M, fun hh => absurd hh (lt_irrefl M)⟩ :
    ∃ h : ℕ, ∀ hh : h < M, ¬ labKey x (j, ⟨h, hh⟩) < labKey x a)

/-- The strings completed after a first wrong guess at the label `a`. -/
noncomputable def cubeFill (x : Fin n → ℝ) (a : Fin n × Fin M) : Fin n → Fin M → Bool :=
  fun j => boxFill M (x j) (if firstOut x a j < M then some (firstOut x a j) else none)

/-- The answer of the emulation. -/
noncomputable def cubeAnswer (M : ℕ) (x : Fin n → ℝ) : Option ℕ → ℝ × Fin n × ℝ
  | none => cubeOracle (fun j => boxFill M (x j) none) x
  | some m => if hm : m < (cubeLabels (M := M) x).length then
      cubeOracle (cubeFill x (cubeLabels (M := M) x)[m]) x
    else cubeOracle (fun j => boxFill M (x j) none) x

omit [NeZero n] in
theorem mem_cubeLabels (x : Fin n → ℝ) (a : Fin n × Fin M) : a ∈ cubeLabels x := by
  unfold cubeLabels
  rw [List.mem_mergeSort, List.mem_product]
  exact ⟨List.mem_finRange _, List.mem_finRange _⟩

omit [NeZero n] in
open Classical in
theorem cubeLabels_sorted (x : Fin n → ℝ) :
    (cubeLabels (M := M) x).Pairwise (fun a b => decide (labKey x a ≤ labKey x b) = true) := by
  unfold cubeLabels
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · intro a b
    rcases le_total (labKey x a) (labKey x b) with h | h <;> simp [h]

omit [NeZero n] in
theorem cubeString_apply (S : Fin n → Fin M → Bool) (a : Fin n × Fin M) :
    cubeString S (finProdFinEquiv a) = S a.1 a.2 := by
  simp [cubeString]

omit [NeZero n] in
theorem firstOut_spec (x : Fin n → ℝ) (a : Fin n × Fin M) (j : Fin n) :
    firstOut x a j ≤ M ∧
      (∀ h (hh : h < M), h < firstOut x a j → labKey x (j, ⟨h, hh⟩) < labKey x a) ∧
      (∀ hh : firstOut x a j < M, ¬ labKey x (j, ⟨firstOut x a j, hh⟩) < labKey x a) := by
  classical
  refine ⟨Nat.find_min' _ (fun hh => absurd hh (lt_irrefl M)), fun h hh hlt => ?_,
    fun hh => Nat.find_spec (⟨M, fun hh => absurd hh (lt_irrefl M)⟩ :
      ∃ h : ℕ, ∀ hh : h < M, ¬ labKey x (j, ⟨h, hh⟩) < labKey x a) hh⟩
  have := Nat.find_min (⟨M, fun hh => absurd hh (lt_irrefl M)⟩ :
    ∃ h : ℕ, ∀ hh : h < M, ¬ labKey x (j, ⟨h, hh⟩) < labKey x a) hlt
  push Not at this
  obtain ⟨hh', h'⟩ := this
  exact h'

theorem cube_emul (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) :
    cubeOracle S x = cubeAnswer M x (stringGuess (cubeString S) (cubeQuery x)) := by
  classical
  have hmatch_iff : ∀ a : Fin n × Fin M,
      (cubeString S (finProdFinEquiv a) != pathBit (x a.1) a.2) = false ↔
        S a.1 a.2 = pathBit (x a.1) a.2 := by
    intro a
    rw [cubeString_apply]
    cases S a.1 a.2 <;> cases pathBit (x a.1) a.2 <;> simp
  cases hans : stringGuess (cubeString S) (cubeQuery x) with
  | none =>
    unfold stringGuess cubeQuery at hans
    rw [List.findIdx?_eq_none_iff] at hans
    have hS : S = fun j => boxFill M (x j) none := by
      funext j k
      have := hans (finProdFinEquiv (j, k), pathBit (x j) k)
        (List.mem_map.mpr ⟨(j, k), mem_cubeLabels x (j, k), rfl⟩)
      exact (hmatch_iff (j, k)).mp this
    rw [hS]
    simp only [cubeAnswer]
  | some m =>
    unfold stringGuess cubeQuery at hans
    rw [List.findIdx?_eq_some_iff_getElem] at hans
    obtain ⟨hm, hmis, hbefore⟩ := hans
    simp only [List.length_map] at hm
    set L := cubeLabels (M := M) x with hL
    set a := L[m] with ha
    have hmis' : S a.1 a.2 ≠ pathBit (x a.1) a.2 := by
      intro h
      have := (hmatch_iff a).mpr h
      simp only [List.getElem_map] at hmis
      rw [this] at hmis
      exact Bool.false_ne_true hmis
    -- every label before `a` in the confidence order was guessed right
    have hbef : ∀ b, labKey x b < labKey x a → S b.1 b.2 = pathBit (x b.1) b.2 := by
      intro b hb
      obtain ⟨p, hp, hpb⟩ := List.mem_iff_getElem.mp (mem_cubeLabels x b)
      rcases lt_trichotomy p m with hpm | hpm | hpm
      · have := hbefore p hpm
        simp only [List.getElem_map, hpb] at this
        exact (hmatch_iff b).mp (by simpa using this)
      · exfalso
        subst hpm
        have hba : b = a := hpb.symm.trans rfl
        rw [hba] at hb
        exact lt_irrefl _ hb
      · exfalso
        have hsorted := List.pairwise_iff_getElem.mp (cubeLabels_sorted (M := M) x) m p hm hp hpm
        simp only [decide_eq_true_eq] at hsorted
        rw [hpb] at hsorted
        exact absurd hb (not_lt.mpr (hsorted : labKey x a ≤ labKey x b))
    set T := cubeFill x a with hT
    -- the bits of every coordinate below its first label after `a` follow the path
    have hpreS : ∀ j (h : Fin M), (h : ℕ) < firstOut x a j → S j h = pathBit (x j) h := by
      intro j h hh
      exact hbef (j, h) ((firstOut_spec x a j).2.1 h h.2 hh)
    -- the coordinate of `a` leaves its path at the bit of `a`
    have hfa : firstOut x a a.1 = a.2 := by
      apply le_antisymm
      · by_contra hlt
        push Not at hlt
        have := (firstOut_spec x a a.1).2.1 a.2 a.2.2 hlt
        exact lt_irrefl _ this
      · by_contra hlt
        push Not at hlt
        have hM : firstOut x a a.1 < M := lt_trans hlt a.2.2
        have hnot := (firstOut_spec x a a.1).2.2 hM
        apply hnot
        rw [labKey_lt_iff]
        have hanti := devVal_anti (M := M) (x a.1) ((a.2 : ℕ) - firstOut x a a.1)
          (firstOut x a a.1) (by omega)
        rw [show firstOut x a a.1 + ((a.2 : ℕ) - firstOut x a a.1) = a.2 by omega] at hanti
        rcases lt_or_eq_of_le hanti with h | h
        · left; exact h
        · right; exact ⟨h.symm, Or.inr ⟨rfl, hlt⟩⟩
    have hTa : T a.1 = boxFill M (x a.1) (some a.2) := by
      simp only [hT, cubeFill, hfa, a.2.2, ↓reduceIte]
    refine (cube_oracle_congr (S := S) (T := T) a.1 ?_ ?_ ?_).trans ?_
    · -- values at the coordinate of `a`
      rw [hTa, value_of_first_dev a.2.2 (fun i hi => hpreS a.1 i (hfa ▸ hi)) hmis']
      rw [devVal, ite_eq_left a.2.2]
    · rw [hTa, oracle_of_first_dev a.2.2 (fun i hi => hpreS a.1 i (hfa ▸ hi)) hmis']
    · intro j hj
      by_cases hfull : firstOut x a j < M
      · right
        have hTj : T j = boxFill M (x j) (some (firstOut x a j)) := by
          simp only [hT, cubeFill, hfull, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · rw [hTj]
          have h1 := value_le_of_prefix (U := S j) (z := x j) (le_of_lt hfull)
            (fun i hi => hpreS j i hi)
          have h2 : devVal M (x j) (firstOut x a j) =
              boxFn (boxFill M (x j) (some (firstOut x a j))) (x j) := by
            rw [devVal, ite_eq_left hfull]
          linarith
        · have hnot := (firstOut_spec x a j).2.2 hfull
          have hne : ((j, ⟨firstOut x a j, hfull⟩) : Fin n × Fin M) ≠ a := by
            intro he
            exact hj (congrArg Prod.fst he)
          have hgt : labKey x a < labKey x (j, ⟨firstOut x a j, hfull⟩) :=
            lt_of_le_of_ne (not_lt.mp hnot) (fun he => hne (labKey_inj x he).symm)
          rw [labKey_lt_iff] at hgt
          have hv : boxFn (T j) (x j) = devVal M (x j) (firstOut x a j) := by
            rw [hTj, devVal, ite_eq_left hfull]
          have hva : boxFn (T a.1) (x a.1) = devVal M (x a.1) a.2 := by
            rw [hTa, devVal, ite_eq_left a.2.2]
          rw [hv, hva]
          rcases hgt with h | ⟨h1, h2 | ⟨h2, -⟩⟩
          · left; exact h
          · right; exact ⟨h1.symm, h2⟩
          · exact absurd h2.symm hj
      · left
        have hfM : firstOut x a j = M := le_antisymm (firstOut_spec x a j).1 (not_lt.mp hfull)
        funext h
        rw [hpreS j h (by rw [hfM]; exact h.2)]
        simp only [hT, cubeFill, hfull, ↓reduceIte]
        rfl
    · show cubeOracle T x = cubeAnswer M x (some m)
      simp only [cubeAnswer]
      rw [dite_eq_left hm]

end Lemmata.OracleComplexity
