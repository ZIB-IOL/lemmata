module

public import Lemmata.FrankWolfePS.Lower.Oracle
public import Lemmata.FrankWolfePS.Lower.Objective
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (I : Finset ι) (v : ι → ℝ) : ℝ := ∑ i ∈ I, v i

theorem completion_mass (P U : Finset ι) (h : ℕ) (hh : 0 < h)
    (hp : Disjoint P U) (v : ι → ℝ) :
    (∑ S ∈ U.powersetCard h, mass (P ∪ S) v) =
      W U.card h * mass P v + V U.card h * mass U v := by
  classical
  have splitS (S : Finset ι) (hs : S ∈ U.powersetCard h) :
      mass (P ∪ S) v = mass P v + mass S v :=
    sum_union (hp.mono_right (mem_powersetCard.mp hs).1)
  rw [sum_congr rfl splitS, sum_add_distrib, sum_const, card_powersetCard, nsmul_eq_mul]
  congr 1
  have expand (S : Finset ι) : mass S v = ∑ i, (if i ∈ S then (1 : ℝ) else 0) * v i := by
    simp [mass, ite_mul]
  simp_rw [expand]
  rw [sum_comm]
  simp_rw [← sum_mul, inclusion_sum U _ hh]
  simp [ite_mul, ← mul_sum]

omit [Fintype ι] [DecidableEq ι] in
private theorem local_young (A : Finset ι) (w : ι → ℝ) (p K : ℝ) :
    4 * K * (p * mass A w) ≤ A.card * p ^ 2 + 4 * K ^ 2 * ∑ i ∈ A, w i ^ 2 := by
  have H := sum_le_sum (s := A) (f := fun i => 4 * K * (p * w i))
    (g := fun i => p ^ 2 + 4 * K ^ 2 * w i ^ 2)
        (fun i _ => by nlinarith [_root_.sq_nonneg (p - 2 * K * w i)])
  simpa only [mass, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum] using H

theorem leaf_mass {k : ℕ} (hk : 0 < k) (z : Pt ι) (P U : Finset ι) (h : ℕ)
    (hpu : Disjoint P U) (hp : P.card ≤ k) (hd : P.card + h = 8 * k) :
    (∑ S ∈ U.powersetCard h, mass (P ∪ S) (guess k z)) ≤ W U.card h / 2 + 2 * V U.card h := by
  classical
  by_cases hav : h ≤ U.card
  · have hh : 0 < h := by omega
    have hn : 0 < (U.card : ℝ) := by exact_mod_cast (show 0 < U.card by omega)
    let θ : ℝ := h / (U.card : ℝ)
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    have hmul : (U.card : ℝ) * θ = h := by dsimp [θ]; field_simp
    have hV : W U.card h * θ = V U.card h := by
      dsimp [θ]; rw [← mul_div_assoc,
          div_eq_iff hn.ne']; nlinarith [marginal_identity (by omega : 0 < U.card) hh]
    let w := guess k z
    have hsum : (∑ i ∈ P, w i ^ 2) + (∑ i ∈ U, w i ^ 2) ≤ sq w := by
      rw [← sum_union hpu]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => _root_.sq_nonneg _
    have hE := guess_energy k z
    change (k : ℝ) * sq w ≤ 1 / 4 at hE
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hp' : (P.card : ℝ) ≤ k := by exact_mod_cast hp
    have hh' : (h : ℝ) ≤ 8 * k := by exact_mod_cast (show h ≤ 8 * k by omega)
    have loc : mass P w + θ * mass U w ≤ 1 / 2 + 2 * θ := by
      apply le_of_mul_le_mul_left (a := 4 * (k : ℝ)) _ (by positivity)
      have H := add_le_add (local_young P w 1 k) (local_young U w θ k)
      have E := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * (k : ℝ) ^ 2)
      have E' := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 4 * (k : ℝ))
      have m := congrArg (fun b : ℝ => b * θ) hmul
      nlinarith [mul_le_mul_of_nonneg_right hh' hθ]
    rw [completion_mass P U h hh hpu, ← hV]
    change W U.card h * mass P w + _ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left loc (show 0 ≤ W U.card h by unfold W; positivity)]
  · rw [powersetCard_eq_empty.mpr (by omega : U.card < h), sum_empty]
    unfold W V; positivity

/-- **Averaging over the completions of a transcript.** If `|P| + h² / |U| ≤ 9k/4`, the squared
norm of the posterior membership vector, the completions `P ∪ S` have mean guessed mass at most
`3/4` (Young's inequality with weight `3k/2`), so one of them has mass at most `3/4`. -/
theorem leaf_average {k : ℕ} (hk : 0 < k) (z : Pt ι) (P U : Finset ι) {h : ℕ}
    (hpu : Disjoint P U) (hh : 0 < h) (hhU : h ≤ U.card)
    (small : 4 * ((P.card : ℝ) * U.card + (h : ℝ) ^ 2) ≤ 9 * k * U.card) :
    ∃ S ∈ U.powersetCard h, mass (P ∪ S) (guess k z) ≤ 3 / 4 := by
  classical
  have hn : 0 < (U.card : ℝ) := by exact_mod_cast (show 0 < U.card by omega)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  let θ : ℝ := h / (U.card : ℝ)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hmul : (U.card : ℝ) * θ = h := by dsimp [θ]; field_simp
  have hV : W U.card h * θ = V U.card h := by
    dsimp [θ]; rw [← mul_div_assoc, div_eq_iff hn.ne']
    nlinarith [marginal_identity (by omega : 0 < U.card) hh]
  let w := guess k z
  have hsum : (∑ i ∈ P, w i ^ 2) + (∑ i ∈ U, w i ^ 2) ≤ sq w := by
    rw [← sum_union hpu]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => _root_.sq_nonneg _
  have hE := guess_energy k z
  change (k : ℝ) * sq w ≤ 1 / 4 at hE
  have hsmall : (P.card : ℝ) + h * θ ≤ 9 * k / 4 := by
    have e : (h : ℝ) * θ * U.card = (h : ℝ) ^ 2 := by rw [mul_assoc, mul_comm θ, hmul]; ring
    have := (le_div_iff₀ hn).mpr (show ((P.card : ℝ) + h * θ) * U.card ≤ 9 * k / 4 * U.card by
      nlinarith)
    rwa [mul_div_assoc, div_self hn.ne', mul_one] at this
  have loc : mass P w + θ * mass U w ≤ 3 / 4 := by
    have H := add_le_add (local_young P w 1 (3 * k / 2)) (local_young U w θ (3 * k / 2))
    have E := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * (3 * (k : ℝ) / 2) ^ 2)
    have hU : (U.card : ℝ) * θ ^ 2 = h * θ := by rw [pow_two, ← mul_assoc, hmul]
    apply le_of_mul_le_mul_left (a := 6 * (k : ℝ)) _ (by positivity)
    nlinarith
  have total : ∑ S ∈ U.powersetCard h, mass (P ∪ S) w ≤
      ∑ S ∈ U.powersetCard h, (3 / 4 : ℝ) := by
    rw [completion_mass P U h hh hpu, ← hV, sum_const, card_powersetCard, nsmul_eq_mul]
    have w0 : 0 ≤ W U.card h := by unfold W; positivity
    change W U.card h * mass P w + W U.card h * θ * mass U w ≤ _
    unfold W at w0 ⊢
    nlinarith [mul_le_mul_of_nonneg_left loc w0]
  exact exists_le_of_sum_le (powersetCard_nonempty.mpr hhU) total

def shells (T : ℕ) (anchor : ι) : Finset (Finset ι) :=
  (univ.erase anchor).powersetCard (8 * (T + 1) - 1)

noncomputable def flag (p : Prop) : ℝ := by classical exact if p then 1 else 0

theorem flag_nonneg (p : Prop) : 0 ≤ flag p := by classical unfold flag; split <;> norm_num

/-- Finite uniform instance average for each fixed tape, for any failure predicate `F` implied by
guessed mass at most `3/4`. The shell `S` represents the hidden instance `insert anchor S`. -/
theorem fixed_tape_mass (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    (F : Finset ι → Pt ι → Prop)
    (hF : ∀ I z, I.card = 8 * (T + 1) → ∑ i ∈ I, guess (T + 1) z i ≤ 3 / 4 → F I z)
    (s : Orders ι (Pt ι) T) :
    (↑(shells T anchor).card : ℝ) / 4 ≤ ∑ S ∈ shells T anchor,
      flag (F (insert anchor S) (s.run (insert anchor S))) := by
  classical
  let k := T + 1
  let U := (univ : Finset ι).erase anchor
  let h := 8 * k - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hn : U.card = 256 * k - 1 := by simp [U, hN, k]
  have hhc : 1 + h = 8 * k := by dsimp [h]; omega
  have hsc : ((shells T anchor).card : ℝ) = W U.card h := by simp [shells, U, W, h, k]
  have H := adaptive_sum s.compile (fun z I => mass I (guess k z)) (leaf_mass hk)
    {anchor} U h (by simp [U]) (by simp [k]; omega) (by simpa using hhc)
  simp only [singleton_union, Orders.run_compile] at H
  change (∑ S ∈ shells T anchor, mass (insert anchor S) (guess k (s.run (insert anchor S)))) ≤
      _ at H
  have hV : 32 * V U.card h ≤ W U.card h := by
    have a := marginal_identity (by omega : 0 < U.card) (by omega : 0 < h)
    have b : 32 * h ≤ U.card := by omega
    have b' : 32 * (h : ℝ) ≤ U.card := by exact_mod_cast b
    have w0 : 0 ≤ W U.card h := by unfold W; positivity
    have hn' : 0 < (U.card : ℝ) := by exact_mod_cast (show 0 < U.card by omega)
    apply le_of_mul_le_mul_left (a := (U.card : ℝ)) _ hn'
    nlinarith [mul_le_mul_of_nonneg_left b' w0]
  have single (S : Finset ι) (hs : S ∈ shells T anchor) :
      (3 / 4 : ℝ) * (1 - flag (F (insert anchor S) (s.run (insert anchor S)))) ≤
        mass (insert anchor S) (guess k (s.run (insert anchor S))) := by
    have hS := mem_powersetCard.mp hs
    have hnS : anchor ∉ S := fun ha => (notMem_erase anchor univ) (hS.1 ha)
    have hcI : (insert anchor S).card = 8 * k := by rw [card_insert_of_notMem hnS, hS.2]; omega
    by_cases bad : F (insert anchor S) (s.run (insert anchor S))
    · simp [flag, bad]; exact sum_nonneg fun i _ => guess_nonneg ..
    · have m := mt (hF _ (s.run (insert anchor S)) hcI) bad
      simpa [flag, bad, mass] using le_of_lt (lt_of_not_ge m)
  have Z := sum_le_sum single
  simp only [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at Z
  change _ ≤ ∑ S ∈ shells T anchor, flag (F (insert anchor S) (s.run (insert anchor S)))
  rw [hsc] at Z ⊢
  linarith

/-- Finite uniform instance average for each fixed tape. The shell S represents
the hidden instance insert anchor S. The actual denominator is the shell cardinality. -/
theorem fixed_tape_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    (R : ℝ) (hR : 0 < R) (s : Orders ι (Pt ι) T) :
    (↑(shells T anchor).card : ℝ) / 4 ≤ ∑ S ∈ shells T anchor,
      flag (failure R (T + 1) (insert anchor S) (s.run (insert anchor S))) :=
  fixed_tape_mass T anchor hN _ (fun _ _ hI hm => small_mass_failure hR (Nat.succ_pos T) hI hm) s

end Lemmata.FrankWolfePS
