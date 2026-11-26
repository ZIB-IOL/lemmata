module

public import Lemmata.AwayStepFW.Pairwise
public import Lemmata.AwayStepFW.Statement

@[expose] public section

/-!
# Pairwise Frank–Wolfe: the linear rate (Theorem 3.2)

Good steps contract the primal gap, drop steps shrink the active set, and fewer than `|V|!` swap
steps can follow each other. Counting gives `t - 1 < (2 |V|! + 2) (G + 1)` for the number `G` of
good steps.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

open Classical in
theorem pairwise_convergence : PairwiseConvergence.{u} := by
  intro E _ _ V f L μ δ x S lam hL hμ hδ hsc hconv hsm hstrong hrun xStar hxs t ht
  set D := Metric.diam (↑V : Set E) with hD
  set ρ := min (1 / 2 : ℝ) (μ * δ ^ 2 / (L * D ^ 2)) with hρ
  set N := V.card.factorial with hN
  set C : ℝ := L * D ^ 2 / 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hρ0 : 0 ≤ ρ := le_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hq0 : 0 ≤ 1 - ρ := by linarith
  have hq1 : 1 - ρ ≤ 1 := by linarith
  have hNpos : 0 < N := Nat.factorial_pos _
  have inv := pfw_run_inv (NNReal.coe_nonneg L) hrun
  have hmono : ∀ s, f (x (s + 1)) ≤ f (x s) := fun s => by
    obtain ⟨v, -, hv, a, -, haS, hstep⟩ := hrun.2.2.2 s
    exact pstep_mono hL hsm (inv s) hv haS hstep
  have hanti : Antitone (fun s => f (x s)) := antitone_nat_of_succ_le hmono
  by_cases hall : ∀ s ≤ t, 0 < f (x s) - f xStar
  swap
  · push Not at hall
    obtain ⟨s, hst, hs⟩ := hall
    have := hanti hst
    have : 0 ≤ (1 - ρ) ^ ((t - 1) / (2 * N + 2)) * C := mul_nonneg (pow_nonneg hq0 _) hC0
    simp only at *
    linarith
  have hP : ∀ n, 1 ≤ n → n ≤ t → ∃ G Dr Sw r t0 : ℕ, G + Dr + Sw + 1 = n ∧
      f (x n) - f xStar ≤ (1 - ρ) ^ G * C ∧ (S n).card + Dr ≤ (S 1).card + G ∧
      Sw ≤ N * (G + Dr) + r ∧ t0 + r = n ∧ r < N ∧
      ∀ k < r, f (x (t0 + k + 1)) < f (x (t0 + k)) ∧ ∃ a ∈ V, ∃ v ∈ V,
        lam (t0 + k + 1) = fun w => lam (t0 + k) (Equiv.swap a v w) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      refine ⟨0, 0, 0, 0, 1, rfl, ?_, le_refl _, by simp, rfl, hNpos,
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      simpa using pfw_first_step hL hconv hsm hxs hrun
    | succ n hn ih =>
      intro hnt
      obtain ⟨G, Dr, Sw, r, t0, hsum, hbd, hcard, hSw, ht0, hrN, hrun'⟩ := ih (by omega)
      obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hrun.2.2.2 n
      have hpos := pfw_pos hL hμ hδ hsc hstrong hxs hrun n (fun s hs => hall s (by omega))
      rcases pstep_outcome hL hμ hδ hsc hsm hstrong hxs (inv n) hpos (hall n (by omega)) hvV hv ha
        haS hstep with ⟨hgood, hc⟩ | ⟨hdrop, hc⟩ | ⟨hswap, hc, hlam⟩
      · refine ⟨G + 1, Dr, Sw, 0, n + 1, by omega, ?_, by omega, ?_, by omega, hNpos,
          fun k hk => absurd hk (Nat.not_lt_zero _)⟩
        · calc f (x (n + 1)) - f xStar ≤ (1 - ρ) * (f (x n) - f xStar) := hgood
            _ ≤ (1 - ρ) * ((1 - ρ) ^ G * C) := mul_le_mul_of_nonneg_left hbd hq0
            _ = (1 - ρ) ^ (G + 1) * C := by ring
        · rw [show G + 1 + Dr = (G + Dr) + 1 by ring, mul_add, mul_one]; omega
      · refine ⟨G, Dr + 1, Sw, 0, n + 1, by omega, by linarith, by omega, ?_, by omega, hNpos,
          fun k hk => absurd hk (Nat.not_lt_zero _)⟩
        rw [show G + (Dr + 1) = (G + Dr) + 1 by ring, mul_add, mul_one]; omega
      · have hrun2 : ∀ k < r + 1, f (x (t0 + k + 1)) < f (x (t0 + k)) ∧ ∃ a ∈ V, ∃ v ∈ V,
            lam (t0 + k + 1) = fun w => lam (t0 + k) (Equiv.swap a v w) := by
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · exact hrun' k hk
          · subst hk
            rw [ht0]
            exact ⟨hswap, a, (inv n).sub ha, v, hvV, hlam⟩
        exact ⟨G, Dr, Sw + 1, r + 1, t0, by omega, by linarith, by omega, by omega, by omega,
          swap_run_bound inv t0 (r + 1) hrun2, hrun2⟩
  obtain ⟨G, Dr, Sw, r, t0, hsum, hbd, hcard, hSw, -, hrN, -⟩ := hP t ht le_rfl
  have hS1 : (S 1).card ≤ 2 := by
    obtain ⟨v, -, -, a, -, -, hstep⟩ := hrun.2.2.2 0
    obtain ⟨-, -, hS'⟩ := hstep
    have h0 : (insert v (S 0)).card ≤ 2 := by
      rw [hrun.2.1]; exact (Finset.card_insert_le _ _).trans (by simp)
    rw [hS']
    split_ifs
    · exact (Finset.card_erase_le).trans h0
    · exact h0
  have hSt : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  have hDr : Dr ≤ G + 1 := by omega
  have hNDr : N * Dr ≤ N * (G + 1) := Nat.mul_le_mul_left N hDr
  have key : t - 1 < (G + 1) * (2 * N + 2) := by
    have e : t - 1 = G + Dr + Sw := by omega
    rw [e]
    nlinarith
  have he : (t - 1) / (2 * N + 2) ≤ G :=
    Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr key)
  calc f (x t) - f xStar ≤ (1 - ρ) ^ G * C := hbd
    _ ≤ (1 - ρ) ^ ((t - 1) / (2 * N + 2)) * C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 he) hC0

end Proof

end Lemmata.AwayStepFW
