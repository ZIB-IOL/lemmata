module

public import Lemmata.LazyCG.Statement

@[expose] public section

/-!
# Weak separation through augmentation (Proposition 6.1)

For `0/1` vectors, `Σ_j (1 - 2 y_j)(z_j - y_j) = ‖z - y‖₁`, so the objective of line 7 adds the
penalty `λ ‖z - y‖₁` to `c z`. A vertex that does not improve it certifies `c(x - z) ≤ Φ`, since the
`ℓ₁`-diameter is at most `k`; an improving vertex shrinks `e = Φ - c(x - y)` by the factor
`1 - 1/k`.
-/

namespace Lemmata.LazyCG

open Lemmata.FrankWolfe

namespace Proof

variable {n : ℕ}

theorem l1_identity {y z : EuclideanSpace ℝ (Fin n)} (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hz : ∀ i, z i = 0 ∨ z i = 1) :
    ∑ j, (1 - 2 * y j) * (z j - y j) = ∑ j, |z j - y j| := by
  apply Finset.sum_congr rfl
  intro j _
  rcases hy j with h | h <;> rcases hz j with h' | h' <;> rw [h, h'] <;> norm_num

theorem aug_diff (c : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) (x y z : EuclideanSpace ℝ (Fin n))
    (Φ k : ℝ) :
    augObjective c x y Φ k z - augObjective c x y Φ k y =
      c z - c y + (Φ - c (x - y)) / k * ∑ j, (1 - 2 * y j) * (z j - y j) := by
  unfold augObjective
  rw [show ∑ j, (1 - 2 * y j) * (z j - y j) =
      ∑ j, (1 - 2 * y j) * z j - ∑ j, (1 - 2 * y j) * y j by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)]
  ring

theorem aug_sep_correct : AugSepCorrect := by
  intro n V c x Φ K k h01 hdiam hk hΦ hK
  have hk0 : 0 < k := by linarith
  have hK0 : 0 < K := by linarith
  refine ⟨fun y hy => ?_, fun y hyV hlt hopt z hz => ?_, fun N xs hN hx0 hcx0 hsteps => ?_⟩
  · have : Φ / K < Φ := div_lt_self hΦ hK
    linarith
  · have hvert : ∀ w ∈ V, c (x - w) ≤ Φ := by
      intro w hw
      have h1 := hopt w hw
      have h2 := aug_diff c x y w Φ k
      rw [l1_identity (h01 y hyV) (h01 w hw)] at h2
      have hlam : 0 ≤ (Φ - c (x - y)) / k := div_nonneg (by linarith) hk0.le
      have h3 : ∑ j, |w j - y j| ≤ k := hdiam w hw y hyV
      have h4 : (Φ - c (x - y)) / k * ∑ j, |w j - y j| ≤ Φ - c (x - y) := by
        calc (Φ - c (x - y)) / k * ∑ j, |w j - y j| ≤ (Φ - c (x - y)) / k * k :=
              mul_le_mul_of_nonneg_left h3 hlam
          _ = Φ - c (x - y) := by field_simp
      rw [map_sub] at h2 h4 ⊢
      linarith
    have hconv : Convex ℝ {w : EuclideanSpace ℝ (Fin n) | c (x - w) ≤ Φ} := by
      have e : {w : EuclideanSpace ℝ (Fin n) | c (x - w) ≤ Φ} = {w | c x - Φ ≤ c w} := by
        ext w
        show c (x - w) ≤ Φ ↔ c x - Φ ≤ c w
        rw [map_sub]
        constructor <;> intro h <;> linarith
      rw [e]
      exact convex_halfSpace_ge (c : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ).isLinear _
    exact convexHull_min (fun w hw => hvert w hw) hconv hz
  · set e : ℕ → ℝ := fun i => Φ - c (x - xs i) with he
    have hstep : ∀ i, 1 ≤ i → i ≤ N → e i < (1 - 1 / k) * e (i - 1) := by
      intro i hi hiN
      obtain ⟨hxi, hlt, himp⟩ := hsteps i hi hiN
      have hxprev : xs (i - 1) ∈ V := by
        rcases Nat.eq_zero_or_pos (i - 1) with h0 | hpos
        · rw [h0]
          exact hx0
        · exact (hsteps (i - 1) hpos (by omega)).1
      have h2 := aug_diff c x (xs (i - 1)) (xs i) Φ k
      rw [l1_identity (h01 _ hxprev) (h01 _ hxi)] at h2
      have hne : xs i ≠ xs (i - 1) := by
        intro h
        rw [h] at himp
        exact lt_irrefl _ himp
      have hl1 : 1 ≤ ∑ j, |xs i j - xs (i - 1) j| := by
        obtain ⟨j, hj⟩ : ∃ j, xs i j ≠ xs (i - 1) j := by
          by_contra hall
          push Not at hall
          exact hne (by ext j; exact hall j)
        have hj1 : |xs i j - xs (i - 1) j| = 1 := by
          rcases h01 _ hxi j with h | h <;> rcases h01 _ hxprev j with h' | h' <;> simp_all
        calc (1 : ℝ) = |xs i j - xs (i - 1) j| := hj1.symm
          _ ≤ ∑ j, |xs i j - xs (i - 1) j| :=
            Finset.single_le_sum (f := fun j => |xs i j - xs (i - 1) j|)
              (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have hlam : 0 < (Φ - c (x - xs (i - 1))) / k := div_pos (by linarith) hk0
      have h3 : c (xs i) - c (xs (i - 1)) +
          (Φ - c (x - xs (i - 1))) / k * ∑ j, |xs i j - xs (i - 1) j| < 0 := by linarith
      have h4 : (Φ - c (x - xs (i - 1))) / k ≤
          (Φ - c (x - xs (i - 1))) / k * ∑ j, |xs i j - xs (i - 1) j| := by
        nlinarith
      have h5 : (Φ - c (x - xs (i - 1))) / k = 1 / k * (Φ - c (x - xs (i - 1))) := by ring
      show Φ - c (x - xs i) < (1 - 1 / k) * (Φ - c (x - xs (i - 1)))
      rw [map_sub] at h3 h4 h5 ⊢
      rw [map_sub]
      nlinarith
    have hN1 : 1 ≤ N := by
      by_contra h
      push Not at h
      have hN0 : N = 0 := by omega
      rw [hN0, pow_zero] at hN
      have : 0 < 1 / K := by positivity
      linarith
    have he0 : e 0 ≤ Φ := by
      show Φ - c (x - xs 0) ≤ Φ
      rw [map_sub]
      linarith
    have he0pos : 0 < e 0 := by
      have := (hsteps 1 le_rfl hN1).2.1
      show 0 < Φ - c (x - xs 0)
      simpa using this
    have hρ0 : 0 ≤ 1 - 1 / k := by
      rw [sub_nonneg, div_le_one hk0]
      exact hk
    have hind : ∀ i, 1 ≤ i → i ≤ N → e i < (1 - 1 / k) ^ i * e 0 := by
      intro i hi hiN
      induction i, hi using Nat.le_induction with
      | base => simpa using hstep 1 le_rfl hiN
      | succ i hi ih =>
        have h1 := hstep (i + 1) (by omega) hiN
        rw [Nat.add_sub_cancel] at h1
        calc e (i + 1) < (1 - 1 / k) * e i := h1
          _ ≤ (1 - 1 / k) * ((1 - 1 / k) ^ i * e 0) :=
            mul_le_mul_of_nonneg_left (ih (by omega)).le hρ0
          _ = (1 - 1 / k) ^ (i + 1) * e 0 := by ring
    have heN := hind N hN1 le_rfl
    have h1 : (1 - 1 / k) ^ N * e 0 ≤ (1 - 1 / K) * e 0 :=
      mul_le_mul_of_nonneg_right hN he0pos.le
    have hK1 : 0 ≤ 1 - 1 / K := by
      rw [sub_nonneg, div_le_one hK0]
      exact hK.le
    have h2 : (1 - 1 / K) * e 0 ≤ (1 - 1 / K) * Φ := mul_le_mul_of_nonneg_left he0 hK1
    have h3 : e N = Φ - c (x - xs N) := rfl
    have h4 : (1 - 1 / K) * Φ = Φ - Φ / K := by ring
    linarith

end Proof

end Lemmata.LazyCG
