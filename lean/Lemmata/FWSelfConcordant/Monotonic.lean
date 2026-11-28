module

public import Lemmata.FWSelfConcordant.Statement
public import Lemmata.FrankWolfe.Proof.Run

@[expose] public section

/-!
# Monotonic Frank–Wolfe (Theorems 2.4 and 2.6)

The iterates stay in `C ∩ D` and in the sublevel set of `x₀`, and `f` decreases. From `T` on, the
local descent property applies to the candidate point: if `γ_t h_t > γ_t² K` the candidate makes
progress and is accepted, and `h_{t+1} ≤ (1 - γ_t) h_t + γ_t² K`; otherwise `h_t ≤ γ_t K` already.
For the Frank–Wolfe gap, either some gap in the last two thirds of the iterations is at most
`γ_t K`, or every step there is accepted and the progress `γ_t g_t` would drive the primal gap
below zero.
-/

namespace Lemmata.FWSelfConcordant

open Lemmata.FrankWolfe

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {C D : Set E} {f : E → ℝ}
  {x v : ℕ → E}

theorem mfw_invariant (hC : Convex ℝ C) (hrun : IsMFWRun C D f x v) :
    ∀ t, x t ∈ C ∧ x t ∈ D ∧ f (x t) ≤ f (x 0) := by
  intro t
  induction t with
  | zero => exact ⟨hrun.1, hrun.2.1, le_rfl⟩
  | succ t ih =>
    obtain ⟨hvC, -, hacc, hrej⟩ := hrun.2.2 t
    by_cases h : x t + (2 / ((t : ℝ) + 2)) • (v t - x t) ∈ D ∧
        f (x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ≤ f (x t)
    · rw [hacc h]
      have ht0 : (0 : ℝ) ≤ t := t.cast_nonneg
      have hγ : (2 / ((t : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩
      exact ⟨hC.add_smul_sub_mem ih.1 hvC hγ, h.1, le_trans h.2 ih.2.2⟩
    · rw [hrej h]; exact ih

theorem mfw_mono (hrun : IsMFWRun C D f x v) (t : ℕ) : f (x (t + 1)) ≤ f (x t) := by
  obtain ⟨-, -, hacc, hrej⟩ := hrun.2.2 t
  by_cases h : x t + (2 / ((t : ℝ) + 2)) • (v t - x t) ∈ D ∧
      f (x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ≤ f (x t)
  · rw [hacc h]; exact h.2
  · rw [hrej h]

theorem mfw_antitone (hrun : IsMFWRun C D f x v) {s t : ℕ} (hst : s ≤ t) :
    f (x t) ≤ f (x s) := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans (mfw_mono hrun t) ih

theorem mfw_gap (hC : Convex ℝ C) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hrun : IsMFWRun C D f x v) (t : ℕ) :
    0 ≤ f (x t) - f xStar ∧ f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) := by
  obtain ⟨hxC, hxD, -⟩ := mfw_invariant hC hrun t
  obtain ⟨-, hvmin, -, -⟩ := hrun.2.2 t
  refine ⟨sub_nonneg.mpr (hxs.2 _ ⟨hxC, hxD⟩), ?_⟩
  have h1 := convexOn_add_fderiv_le hconv ⟨hxC, hxD⟩ (hdiff _ ⟨hxC, hxD⟩) hxs.1
  have h2 := hvmin xStar hxs.1.1
  rw [map_sub] at h1 ⊢
  linarith

/-- From `T` on, the candidate satisfies the local descent bound. -/
theorem mfw_step (hC : Convex ℝ C) {K : ℝ} {T : ℕ} (hrun : IsMFWRun C D f x v)
    (hdesc : HasLocalDescent C D f (x 0) (2 / ((T : ℝ) + 2)) K) (t : ℕ) (ht : T ≤ t) :
    x t + (2 / ((t : ℝ) + 2)) • (v t - x t) ∈ D ∧
      f (x t + (2 / ((t : ℝ) + 2)) • (v t - x t)) ≤
        f (x t) - 2 / ((t : ℝ) + 2) * fderiv ℝ f (x t) (x t - v t) +
          (2 / ((t : ℝ) + 2)) ^ 2 * K := by
  obtain ⟨hxC, hxD, hxf⟩ := mfw_invariant hC hrun t
  obtain ⟨hvC, -, -, -⟩ := hrun.2.2 t
  have hγ : (2 / ((t : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) (2 / ((T : ℝ) + 2)) := by
    refine ⟨by positivity, ?_⟩
    have : (T : ℝ) ≤ t := by exact_mod_cast ht
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  obtain ⟨h1, h2⟩ := hdesc (x t) hxC hxD hxf (v t) hvC _ hγ
  refine ⟨h1, ?_⟩
  have e : fderiv ℝ f (x t) (v t - x t) = -fderiv ℝ f (x t) (x t - v t) := by
    rw [← map_neg, neg_sub]
  rw [e] at h2
  linarith

/-- The algebra of the induction step. -/
theorem rate_step (T t : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (1 - 2 / ((t : ℝ) + 2)) * (4 * ((T : ℝ) + 1) / ((t : ℝ) + 1) * B) +
        (2 / ((t : ℝ) + 2)) ^ 2 * B ≤ 4 * ((T : ℝ) + 1) / ((t : ℝ) + 2) * B := by
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  have hT : (0 : ℝ) ≤ T := T.cast_nonneg
  have key : 4 * ((T : ℝ) + 1) / ((t : ℝ) + 2) -
      ((1 - 2 / ((t : ℝ) + 2)) * (4 * ((T : ℝ) + 1) / ((t : ℝ) + 1)) + (2 / ((t : ℝ) + 2)) ^ 2) =
      4 / ((t : ℝ) + 2) * (((T : ℝ) + 1) / ((t : ℝ) + 1) - 1 / ((t : ℝ) + 2)) := by
    field_simp; ring
  have hpos : 0 ≤ 4 / ((t : ℝ) + 2) * (((T : ℝ) + 1) / ((t : ℝ) + 1) - 1 / ((t : ℝ) + 2)) := by
    apply mul_nonneg (by positivity)
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  nlinarith

theorem monotonic_rate_bound (hC : Convex ℝ C) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hrun : IsMFWRun C D f x v) {K : ℝ} (hK : 0 ≤ K) {T : ℕ}
    (hdesc : HasLocalDescent C D f (x 0) (2 / ((T : ℝ) + 2)) K) :
    ∀ t : ℕ, T ≤ t →
      f (x t) - f xStar ≤ 4 * ((T : ℝ) + 1) / ((t : ℝ) + 1) * max (f (x 0) - f xStar) K := by
  set B := max (f (x 0) - f xStar) K with hB
  have hB0 : 0 ≤ B := le_trans hK (le_max_right _ _)
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have h1 := mfw_antitone hrun (Nat.zero_le T)
    have h2 : f (x 0) - f xStar ≤ B := le_max_left _ _
    have e : 4 * ((T : ℝ) + 1) / ((T : ℝ) + 1) * B = 4 * B := by field_simp
    rw [e]; linarith
  | succ t ht ih =>
    obtain ⟨hgap0, hgap⟩ := mfw_gap hC hconv hdiff hxs hrun t
    obtain ⟨hcD, hcf⟩ := mfw_step hC hrun hdesc t ht
    set γ := 2 / ((t : ℝ) + 2) with hγ
    have hγ0 : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 := by
      rw [hγ, div_le_one (by positivity)]; linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)]
    have hKB : K ≤ B := le_max_right _ _
    push_cast
    rw [show (t : ℝ) + 1 + 1 = (t : ℝ) + 2 by ring]
    by_cases hcase : γ ^ 2 * K < γ * (f (x t) - f xStar)
    · -- progress: the candidate is accepted
      have hprog : f (x t + γ • (v t - x t)) ≤ f (x t) := by nlinarith
      obtain ⟨-, -, hacc, -⟩ := hrun.2.2 t
      rw [hacc ⟨hcD, hprog⟩]
      have h1 : f (x t + γ • (v t - x t)) - f xStar ≤
          (1 - γ) * (f (x t) - f xStar) + γ ^ 2 * K := by nlinarith
      have h2 : (1 - γ) * (f (x t) - f xStar) ≤
          (1 - γ) * (4 * ((T : ℝ) + 1) / ((t : ℝ) + 1) * B) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have h3 : γ ^ 2 * K ≤ γ ^ 2 * B := mul_le_mul_of_nonneg_left hKB (by positivity)
      have h4 := rate_step T t hB0
      linarith
    · -- no guaranteed progress: `h_t ≤ γ K`
      push Not at hcase
      have h1 : f (x t) - f xStar ≤ γ * K := by
        have := hcase
        rw [sq, mul_assoc] at this
        exact le_of_mul_le_mul_left this hγ0
      have h2 := mfw_mono hrun t
      have h3 : γ * K ≤ 4 * ((T : ℝ) + 1) / ((t : ℝ) + 2) * B := by
        rw [hγ]
        have hT : (0 : ℝ) ≤ T := T.cast_nonneg
        calc 2 / ((t : ℝ) + 2) * K ≤ 2 / ((t : ℝ) + 2) * B :=
              mul_le_mul_of_nonneg_left hKB (by positivity)
          _ ≤ 4 * ((T : ℝ) + 1) / ((t : ℝ) + 2) * B := by
              apply mul_le_mul_of_nonneg_right _ hB0
              apply div_le_div_of_nonneg_right _ (by positivity)
              linarith
      linarith

set_option maxHeartbeats 1000000 in
theorem monotonic_gap_bound (hC : Convex ℝ C) (hconv : ConvexOn ℝ (C ∩ D) f)
    (hdiff : ∀ y ∈ C ∩ D, DifferentiableAt ℝ f y) {xStar : E} (hxs : xStar ∈ minimizers (C ∩ D) f)
    (hrun : IsMFWRun C D f x v) {K : ℝ} (hK : 0 ≤ K) {T : ℕ}
    (hdesc : HasLocalDescent C D f (x 0) (2 / ((T : ℝ) + 2)) K) (hT1 : 1 ≤ T) (N : ℕ)
    (hN : T + 6 ≤ N) :
    ∃ t, 1 ≤ t ∧ t ≤ N ∧ fderiv ℝ f (x t) (x t - v t) ≤
      18 * (N : ℝ) / ((N : ℝ) - T) * (((T : ℝ) + 1) / (2 * (T : ℝ) + N - 3) +
        (2 * (N : ℝ) - 2 * T + 3) / (2 * (T : ℝ) + N) ^ 2) * max (f (x 0) - f xStar) K := by
  set B := max (f (x 0) - f xStar) K with hB
  have hB0 : 0 ≤ B := le_trans hK (le_max_right _ _)
  have hKB : K ≤ B := le_max_right _ _
  set A₁ := ((T : ℝ) + 1) / (2 * (T : ℝ) + N - 3) with hA₁
  set A₂ := (2 * (N : ℝ) - 2 * T + 3) / (2 * (T : ℝ) + N) ^ 2 with hA₂
  set bound := 18 * (N : ℝ) / ((N : ℝ) - T) * (A₁ + A₂) * B with hbound
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hNr : (T : ℝ) + 6 ≤ N := by exact_mod_cast hN
  have hA₁0 : 0 ≤ A₁ := div_nonneg (by linarith) (by linarith)
  have hA₂0 : 0 ≤ A₂ := div_nonneg (by linarith) (by positivity)
  have hNT : 0 < (N : ℝ) - T := by linarith
  have hbound0 : 0 ≤ bound := by
    rw [hbound]; apply mul_nonneg (mul_nonneg (div_nonneg (by linarith) hNT.le) (by linarith)) hB0
  by_contra hcon
  push Not at hcon
  -- the window `[tmin, tmax]`
  set c := (N - T + 2) / 3 with hc
  have hc3 : N - T ≤ 3 * c ∧ 3 * c ≤ N - T + 2 := by omega
  set tmin := T + c - 2 with htmin
  set tmax := N - 2 with htmax
  have htmin1 : 1 ≤ tmin := by omega
  have hTtmin : T ≤ tmin := by omega
  have htmm : tmin ≤ tmax := by omega
  have e1 : (tmin : ℝ) + 2 = T + c := by
    have : tmin + 2 = T + c := by omega
    exact_mod_cast this
  have e2 : (3 : ℝ) * c + T ≤ N + 2 := by
    have : 3 * c + T ≤ N + 2 := by omega
    exact_mod_cast this
  have e3 : (N : ℝ) ≤ 3 * c + T := by
    have : N ≤ 3 * c + T := by omega
    exact_mod_cast this
  have e4 : (tmax : ℝ) + 2 = N := by
    have : tmax + 2 = N := by omega
    exact_mod_cast this
  set r := tmax + 1 - tmin with hr
  have e5 : (r : ℝ) + c + T = N + 1 := by
    have : r + c + T = N + 1 := by omega
    exact_mod_cast this
  have hr_lo : 2 * ((N : ℝ) - T) / 3 ≤ r := by linarith
  have hr_hi : (r : ℝ) ≤ (2 * (N : ℝ) - 2 * T + 3) / 3 := by linarith
  have ht1 : (2 * (T : ℝ) + N - 3) / 3 ≤ (tmin : ℝ) + 1 := by linarith
  have ht2 : (2 * (T : ℝ) + N) / 3 ≤ (tmin : ℝ) + 2 := by linarith
  have hpos1 : 0 < (2 * (T : ℝ) + N - 3) / 3 := by linarith
  have hpos2 : 0 < (2 * (T : ℝ) + N) / 3 := by linarith
  by_cases hcase : ∃ k, tmin ≤ k ∧ k ≤ tmax ∧
      2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k) ≤ (2 / ((k : ℝ) + 2)) ^ 2 * K
  · obtain ⟨k, hk1, hk2, hk⟩ := hcase
    have hγ0 : 0 < 2 / ((k : ℝ) + 2) := by positivity
    have hgk : fderiv ℝ f (x k) (x k - v k) ≤ 2 / ((k : ℝ) + 2) * K := by
      rw [sq, mul_assoc] at hk; exact le_of_mul_le_mul_left hk hγ0
    have hkr : (tmin : ℝ) ≤ k := by exact_mod_cast hk1
    have hγk : 2 / ((k : ℝ) + 2) ≤ 6 / (2 * (T : ℝ) + N) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith
    have h6 : 6 / (2 * (T : ℝ) + N) * B ≤ bound := by
      rw [hbound]
      apply mul_le_mul_of_nonneg_right _ hB0
      have hNpos : (0 : ℝ) < N := by linarith
      have h1 : 18 * (N : ℝ) / ((N : ℝ) - T) * A₂ ≤ 18 * (N : ℝ) / ((N : ℝ) - T) * (A₁ + A₂) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hNT.le)
      refine le_trans ?_ h1
      rw [hA₂, div_mul_div_comm, div_le_div_iff₀ (by linarith) (by positivity)]
      have hfac : 18 * (N : ℝ) * (2 * (N : ℝ) - 2 * T + 3) * (2 * (T : ℝ) + N) -
          6 * (((N : ℝ) - T) * (2 * (T : ℝ) + N) ^ 2) =
          6 * (2 * (T : ℝ) + N) * ((5 * (N : ℝ) - 2 * T) * ((N : ℝ) - T) + 9 * N) := by ring
      have hnn : 0 ≤ 6 * (2 * (T : ℝ) + N) * ((5 * (N : ℝ) - 2 * T) * ((N : ℝ) - T) + 9 * N) := by
        apply mul_nonneg (by linarith)
        have : 0 ≤ (5 * (N : ℝ) - 2 * T) * ((N : ℝ) - T) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      linarith
    have := hcon k (by omega) (by omega)
    have h7 : 2 / ((k : ℝ) + 2) * K ≤ 6 / (2 * (T : ℝ) + N) * B :=
      mul_le_mul hγk hKB hK (by positivity)
    linarith
  · push Not at hcase
    have hstep : ∀ k, tmin ≤ k → k ≤ tmax →
        f (x (k + 1)) - f xStar ≤ f (x k) - f xStar -
          2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k) + (2 / ((k : ℝ) + 2)) ^ 2 * K := by
      intro k hk1 hk2
      obtain ⟨hcD, hcf⟩ := mfw_step hC hrun hdesc k (by omega)
      have hprog : f (x k + (2 / ((k : ℝ) + 2)) • (v k - x k)) ≤ f (x k) := by
        linarith [hcase k hk1 hk2]
      obtain ⟨-, -, hacc, -⟩ := hrun.2.2 k
      rw [hacc ⟨hcD, hprog⟩]
      linarith
    have htel : ∀ j, tmin ≤ j → j ≤ tmax + 1 →
        f (x j) - f xStar ≤ f (x tmin) - f xStar + ∑ k ∈ Finset.Ico tmin j,
          ((2 / ((k : ℝ) + 2)) ^ 2 * K - 2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k)) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; simp
      | succ j hj ih =>
        intro hj2
        rw [Finset.sum_Ico_succ_top hj]
        have h1 := hstep j hj (by omega)
        have h2 := ih (by omega)
        linarith
    have hfin := htel (tmax + 1) (by omega) le_rfl
    set I := Finset.Ico tmin (tmax + 1) with hI
    have hIcard : (I.card : ℝ) = r := by rw [hI, Nat.card_Ico]
    have hIne : I.Nonempty := ⟨tmin, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have hterm : ∀ k ∈ I, (2 / ((k : ℝ) + 2)) ^ 2 * K -
        2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k) <
          (2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound := by
      intro k hk
      rw [hI, Finset.mem_Ico] at hk
      have hgk := hcon k (by omega) (by omega)
      have hkr1 : (tmin : ℝ) ≤ k := by exact_mod_cast hk.1
      have hkr2 : (k : ℝ) + 2 ≤ N := by
        have : k + 2 ≤ N := by omega
        exact_mod_cast this
      have hγ1 : 2 / ((k : ℝ) + 2) ≤ 2 / ((tmin : ℝ) + 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have hγ2 : 2 / (N : ℝ) ≤ 2 / ((k : ℝ) + 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hkr2
      have hγ0 : 0 < 2 / ((k : ℝ) + 2) := by positivity
      have i1 : (2 / ((k : ℝ) + 2)) ^ 2 * K ≤ (2 / ((tmin : ℝ) + 2)) ^ 2 * B :=
        mul_le_mul (pow_le_pow_left₀ hγ0.le hγ1 2) hKB hK (by positivity)
      have i2 : 2 / (N : ℝ) * bound < 2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hγ2 hbound0) (mul_lt_mul_of_pos_left hgk hγ0)
      linarith
    have hsum : ∑ k ∈ I, ((2 / ((k : ℝ) + 2)) ^ 2 * K -
        2 / ((k : ℝ) + 2) * fderiv ℝ f (x k) (x k - v k)) <
          (r : ℝ) * ((2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound) := by
      calc _ < ∑ k ∈ I, ((2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound) :=
            Finset.sum_lt_sum_of_nonempty hIne hterm
        _ = (r : ℝ) * ((2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound) := by
            rw [Finset.sum_const, nsmul_eq_mul, hIcard]
    have hhmin := monotonic_rate_bound hC hconv hdiff hxs hrun hK hdesc tmin hTtmin
    have h0 := (mfw_gap hC hconv hdiff hxs hrun (tmax + 1)).1
    -- the three estimates
    have s1 : 4 * ((T : ℝ) + 1) / ((tmin : ℝ) + 1) ≤ 12 * A₁ := by
      rw [hA₁]
      calc 4 * ((T : ℝ) + 1) / ((tmin : ℝ) + 1) ≤ 4 * ((T : ℝ) + 1) / ((2 * (T : ℝ) + N - 3) / 3) :=
            div_le_div_of_nonneg_left (by linarith) hpos1 ht1
        _ = 12 * (((T : ℝ) + 1) / (2 * (T : ℝ) + N - 3)) := by field_simp; ring
    have s2 : (r : ℝ) * (2 / ((tmin : ℝ) + 2)) ^ 2 ≤ 12 * A₂ := by
      rw [hA₂]
      have hsq : ((2 * (T : ℝ) + N) / 3) ^ 2 ≤ ((tmin : ℝ) + 2) ^ 2 :=
        pow_le_pow_left₀ hpos2.le ht2 2
      calc (r : ℝ) * (2 / ((tmin : ℝ) + 2)) ^ 2 = (r : ℝ) * 4 / ((tmin : ℝ) + 2) ^ 2 := by
            rw [div_pow]; ring
        _ ≤ ((2 * (N : ℝ) - 2 * T + 3) / 3) * 4 / ((2 * (T : ℝ) + N) / 3) ^ 2 := by
            apply div_le_div₀ (by linarith) (by linarith) (by positivity) hsq
        _ = 12 * ((2 * (N : ℝ) - 2 * T + 3) / (2 * (T : ℝ) + N) ^ 2) := by field_simp; ring
    have s3 : 24 * (A₁ * B) + 24 * (A₂ * B) ≤ (r : ℝ) * (2 / (N : ℝ) * bound) := by
      rw [hbound]
      have hNpos : (0 : ℝ) < N := by linarith
      have e : (r : ℝ) * (2 / (N : ℝ) * (18 * (N : ℝ) / ((N : ℝ) - T) * (A₁ + A₂) * B)) =
          36 * (r : ℝ) / ((N : ℝ) - T) * ((A₁ + A₂) * B) := by
        field_simp; ring
      rw [e]
      have h36 : 24 ≤ 36 * (r : ℝ) / ((N : ℝ) - T) := by
        rw [le_div_iff₀ hNT]; linarith
      have hAB : 0 ≤ (A₁ + A₂) * B := mul_nonneg (by linarith) hB0
      have := mul_le_mul_of_nonneg_right h36 hAB
      have e2 : 24 * ((A₁ + A₂) * B) = 24 * (A₁ * B) + 24 * (A₂ * B) := by ring
      linarith
    have hfinal : 4 * ((T : ℝ) + 1) / ((tmin : ℝ) + 1) * B +
        (r : ℝ) * ((2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound) ≤ 0 := by
      have i1 : 4 * ((T : ℝ) + 1) / ((tmin : ℝ) + 1) * B ≤ 12 * A₁ * B :=
        mul_le_mul_of_nonneg_right s1 hB0
      have i2 : (r : ℝ) * (2 / ((tmin : ℝ) + 2)) ^ 2 * B ≤ 12 * A₂ * B :=
        mul_le_mul_of_nonneg_right s2 hB0
      have e : (r : ℝ) * ((2 / ((tmin : ℝ) + 2)) ^ 2 * B - 2 / (N : ℝ) * bound) =
          (r : ℝ) * (2 / ((tmin : ℝ) + 2)) ^ 2 * B - (r : ℝ) * (2 / (N : ℝ) * bound) := by ring
      have e1 : 12 * A₁ * B = 12 * (A₁ * B) := by ring
      have e2 : 12 * A₂ * B = 12 * (A₂ * B) := by ring
      have hA1B : 0 ≤ A₁ * B := mul_nonneg hA₁0 hB0
      have hA2B : 0 ≤ A₂ * B := mul_nonneg hA₂0 hB0
      linarith
    linarith

namespace Proof

theorem monotonic_rate : MonotonicRate.{u} := by
  intro E _ _ C D f x v xStar K T hC _ hconv hdiff hxs hrun hK hdesc t ht
  exact monotonic_rate_bound hC hconv hdiff hxs hrun hK hdesc t ht

theorem monotonic_gap_rate : MonotonicGapRate.{u} := by
  intro E _ _ C D f x v xStar K T hC _ hconv hdiff hxs hrun hK hdesc hT1 N hN
  exact monotonic_gap_bound hC hconv hdiff hxs hrun hK hdesc hT1 N hN

end Proof

end Lemmata.FWSelfConcordant
