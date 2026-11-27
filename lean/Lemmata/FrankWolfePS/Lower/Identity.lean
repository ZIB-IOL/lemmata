module

public import Lemmata.FrankWolfePS.Lower.Numerical

@[expose] public section

/-!
# The exact posterior identity

Run a membership tree on a hidden set drawn uniformly from the completions of a transcript. At
the end, let `h` be the number of hidden labels not yet found and `U` the set of labels not yet
tested. Then the expected ratio `h / |U|` equals its initial value: a fresh test is positive with
probability `h / |U|`, after which the ratio is `(h - 1)/(|U| - 1)`, and negative otherwise, after
which it is `h/(|U| - 1)`; the weighted mean is `h / |U|`. In counting form, the sum over the
completions is `C(|U| - 1, h - 1)`, by Pascal's rule along each probe.
-/

namespace Lemmata.FrankWolfePS
open Finset

section Tree
variable {ι O : Type*} [DecidableEq ι]

/-- The labels not yet tested and the number of hidden labels not yet found, after running the
tree on the hidden set `I` from the state `(U, h)`. -/
def Tree.posterior {t} : Tree ι O t → Finset ι → Finset ι → ℕ → Finset ι × ℕ
  | .leaf _, _, U, h => (U, h)
  | .pass s, I, U, h => s.posterior I U h
  | .probe i miss hit, I, U, h =>
      if i ∈ I then hit.posterior I (U.erase i) (if i ∈ U then h - 1 else h)
      else miss.posterior I (U.erase i) h

/-- The final ratio `h / |U|`. -/
noncomputable def Tree.ratio {t} (s : Tree ι O t) (I U : Finset ι) (h : ℕ) : ℝ :=
  ((s.posterior I U h).2 : ℝ) / ((s.posterior I U h).1.card : ℝ)

/-- **The posterior identity**, in counting form. -/
theorem ratio_sum {k t : ℕ} (hk : 0 < k) (s : Tree ι O t) (P U : Finset ι) (h : ℕ)
    (hPU : Disjoint P U) (calls : P.card + t ≤ k) (size : P.card + h = 8 * k) :
    ∑ S ∈ U.powersetCard h, s.ratio (P ∪ S) U h = V U.card h := by
  induction s generalizing P U h with
  | leaf x =>
    simp only [Tree.ratio, Tree.posterior, sum_const, card_powersetCard, nsmul_eq_mul]
    have h2 : 2 ≤ h := by omega
    rcases Nat.eq_zero_or_pos U.card with hn | hn
    · rw [hn, Nat.choose_eq_zero_of_lt (by omega : 0 < h)]
      simp [V, Nat.choose_eq_zero_of_lt (show 0 < h - 1 by omega)]
    · have mi := marginal_identity hn (by omega : 0 < h)
      unfold W at mi
      have hn' : (U.card : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      linarith [mi]
  | pass s ih =>
    simp only [Tree.ratio, Tree.posterior] at ih ⊢
    exact ih P U h hPU (by omega) size
  | @probe t i miss hit ihm ihy =>
    by_cases ip : i ∈ P
    · have iU : i ∉ U := fun h => disjoint_left.mp hPU ip h
      have e : ∀ S ∈ U.powersetCard h, (Tree.probe i miss hit).ratio (P ∪ S) U h =
          hit.ratio (P ∪ S) U h := fun S _ => by
        simp [Tree.ratio, Tree.posterior, ip, iU]
      rw [sum_congr rfl e]
      exact ihy P U h hPU (by omega) size
    by_cases iu : i ∈ U
    · by_cases avail : h ≤ U.card
      · have ih2 : 2 ≤ h := by omega
        obtain ⟨j, hj⟩ : ∃ j, h = j + 2 := ⟨h - 2, by omega⟩
        subst h
        let A := U.erase i
        have hn : U.card = A.card + 1 := by
          dsimp [A]; rw [card_erase_of_mem iu]; have := card_pos.mpr ⟨i, iu⟩; omega
        have hA : Disjoint P A := hPU.mono_right (erase_subset _ _)
        have hPA : Disjoint (insert i P) A := by simpa [A, disjoint_insert_left] using hA
        have hm := ihm P A (j + 2) hA calls size
        have hy := ihy (insert i P) A (j + 1) hPA
          (by rw [card_insert_of_notMem ip]; omega) (by rw [card_insert_of_notMem ip]; omega)
        rw [sum_split U iu (j + 1)]
        have eqm : ∀ S ∈ A.powersetCard (j + 2), (Tree.probe i miss hit).ratio (P ∪ S) U (j + 2) =
            miss.ratio (P ∪ S) A (j + 2) := fun S hs => by
          have hiS : i ∉ S := fun hi => (notMem_erase i U) ((mem_powersetCard.mp hs).1 hi)
          simp [Tree.ratio, Tree.posterior, ip, hiS, A]
        have eqy : ∀ S ∈ A.powersetCard (j + 1),
            (Tree.probe i miss hit).ratio (P ∪ insert i S) U (j + 2) =
              hit.ratio (insert i P ∪ S) A (j + 1) := fun S _ => by
          have e : P ∪ insert i S = insert i P ∪ S := by ext a; simp
          simp [Tree.ratio, Tree.posterior, e, iu, A]
        rw [show U.erase i = A from rfl, sum_congr rfl eqm, sum_congr rfl eqy, hm, hy]
        have npos : 0 < A.card := by omega
        obtain ⟨n, hna⟩ := Nat.exists_eq_succ_of_ne_zero npos.ne'
        rw [hn, hna]; simp [V, Nat.choose_succ_succ, add_comm]
      · have e : U.powersetCard h = ∅ := powersetCard_eq_empty.mpr (by omega)
        rw [e, sum_empty]
        simp [V, Nat.choose_eq_zero_of_lt (show U.card - 1 < h - 1 by omega)]
    · have e : ∀ S ∈ U.powersetCard h, (Tree.probe i miss hit).ratio (P ∪ S) U h =
          miss.ratio (P ∪ S) U h := fun S hs => by
        have hiS : i ∉ S := fun hi => iu ((mem_powersetCard.mp hs).1 hi)
        simp [Tree.ratio, Tree.posterior, ip, hiS, erase_eq_of_notMem iu]
      rw [sum_congr rfl e]
      exact ihm P U h hPU calls size

end Tree

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The posterior identity (Lemma 2).** For every method requiring no more than `T` calls to
the vertex oracle, the final ratio of hidden labels not yet found to labels not yet tested,
averaged over the uniform prior on the hidden sets, equals `(d - 1)/(N - 1)` with
`d = 8(T + 1)` and `N = 256(T + 1)`. -/
theorem posterior_identity (T : ℕ) (a : ι) (hN : Fintype.card ι = 256 * (T + 1))
    (s : Method (Ambient ι) T) (R : ℝ) :
    ∑ S ∈ shells T a, (s.orders R a).compile.ratio (insert a S) (univ.erase a) (8 * (T + 1) - 1) =
      (shells T a).card * (((8 * (T + 1) - 1 : ℕ) : ℝ) / ((256 * (T + 1) - 1 : ℕ) : ℝ)) := by
  have hU : (univ.erase a).card = 256 * (T + 1) - 1 := by simp [hN]
  have H := ratio_sum (k := T + 1) (Nat.succ_pos T) (s.orders R a).compile {a} (univ.erase a)
    (8 * (T + 1) - 1) (by simp) (by simp; omega) (by simp; omega)
  simp only [singleton_union] at H
  rw [shells, H, hU, card_powersetCard, hU]
  have mi := marginal_identity (n := 256 * (T + 1) - 1) (h := 8 * (T + 1) - 1) (by omega) (by omega)
  unfold W at mi
  have hpos : (0 : ℝ) < ((256 * (T + 1) - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 256 * (T + 1) - 1)
  rw [mul_div_assoc', eq_div_iff hpos.ne']
  linarith [mi]

end Lemmata.FrankWolfePS
