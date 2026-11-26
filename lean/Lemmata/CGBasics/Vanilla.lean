module

public import Lemmata.CGBasics.Approx

@[expose] public section

/-!
# Vanilla Frank–Wolfe: primal and Frank–Wolfe gaps (Theorems 2.2 and 2.11)

A step with Frank–Wolfe gap `g` gains at least `g²/(2 L D²)` when `g ≤ L D²` (take `s = g/(L D²)`)
and at least `g - L D²/2` in any case (take `s = 1`). If all gaps up to `t` were too large, the
gains would add up to more than the primal gap allows.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem step_facts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {f : E → ℝ}
    {L : NNReal} (hbdd : Bornology.IsBounded C) {x v : E} (hx : x ∈ C) (hv : v ∈ C)
    (hlmo : ∀ y ∈ C, fderiv ℝ f x v ≤ fderiv ℝ f x y) {x' : E}
    (hstep : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      f x' ≤ f x - s * fderiv ℝ f x (x - v) + s ^ 2 * L / 2 * ‖v - x‖ ^ 2) :
    0 ≤ fderiv ℝ f x (x - v) ∧
      f x' ≤ f x - fderiv ℝ f x (x - v) + L * Metric.diam C ^ 2 / 2 ∧
      (0 < (L : ℝ) * Metric.diam C ^ 2 → fderiv ℝ f x (x - v) ≤ L * Metric.diam C ^ 2 →
        f x' ≤ f x - fderiv ℝ f x (x - v) ^ 2 / (2 * (L * Metric.diam C ^ 2))) := by
  set g := fderiv ℝ f x (x - v) with hgdef
  set K : ℝ := L * Metric.diam C ^ 2 with hK
  have hg : 0 ≤ g := by
    have := hlmo x hx
    rw [hgdef, map_sub]; linarith
  have hd : ‖v - x‖ ≤ Metric.diam C := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hbdd hv hx
  have hd2 : (L : ℝ) * ‖v - x‖ ^ 2 ≤ K :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) (NNReal.coe_nonneg L)
  refine ⟨hg, ?_, ?_⟩
  · have := hstep 1 ⟨zero_le_one, le_refl _⟩
    nlinarith
  · intro hKpos hgK
    set s := g / K with hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg hg hKpos.le, (div_le_one hKpos).mpr hgK⟩
    have h0 := hstep s hs01
    have h1 : s ^ 2 * L / 2 * ‖v - x‖ ^ 2 ≤ s ^ 2 * K / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hd2 (sq_nonneg s)]
    have h2 : s * g - s ^ 2 * K / 2 = g ^ 2 / (2 * K) := by
      rw [hs]; field_simp; ring
    linarith

/-- The iterates stay in `C`. -/
theorem iterates_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hCc : Convex ℝ C) {x v : ℕ → E} {γ : ℕ → ℝ} (hx0 : x 0 ∈ C)
    (hrun : ∀ t : ℕ, v t ∈ C ∧ γ t ∈ Set.Icc (0 : ℝ) 1 ∧ x (t + 1) = x t + γ t • (v t - x t)) :
    ∀ t, x t ∈ C := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    rw [(hrun t).2.2]
    exact hCc.add_smul_sub_mem ih (hrun t).1 (hrun t).2.1

/-- `(t + 3)² ≤ 4 (t₀ + 3)(t - t₀ + 1)` for `t₀ = ⌊(t + 1)/2⌋`. -/
theorem half_split (t : ℕ) :
    ((t : ℝ) + 3) ^ 2 ≤ 4 * (((t + 1) / 2 : ℕ) + 3) * ((t - (t + 1) / 2 + 1 : ℕ) : ℝ) := by
  rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
  · have e1 : (2 * k + 1) / 2 = k := by omega
    have e2 : 2 * k - k + 1 = k + 1 := by omega
    rw [e1, e2]; push_cast; nlinarith
  · have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have e2 : 2 * k + 1 - (k + 1) + 1 = k + 1 := by omega
    rw [e1, e2]; push_cast; nlinarith

theorem vanilla_rate : VanillaRate.{u} := by
  intro E _ _ C f L x v γ hC hCc hconv hsm hx0 hrun xStar hxs t ht
  set D := Metric.diam C with hD
  set K : ℝ := L * D ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hbdd := hC.isBounded
  have hprimal : ∀ τ : ℕ, 1 ≤ τ → f (x τ) - f xStar ≤ 2 * K / ((τ : ℝ) + 3) := by
    intro τ hτ
    have := approximate_oracle_rate C f L 0 x v γ hC hCc hconv hsm le_rfl hx0
      (fun t => ⟨(hrun t).1, fun y hy => by simpa using (hrun t).2.1 y hy, (hrun t).2.2⟩)
      xStar hxs τ hτ
    have e : 2 * (L : ℝ) * D ^ 2 * (1 + 0) / ((τ : ℝ) + 3) = 2 * K / ((τ : ℝ) + 3) := by
      rw [hK]; ring
    linarith
  have hxC := iterates_mem hCc hx0 (fun t => ⟨(hrun t).1, (hrun t).2.2.1, (hrun t).2.2.2.1⟩)
  have hfacts := fun τ => step_facts (L := L) hbdd (hxC τ) (hrun τ).1 (hrun τ).2.1
    (hrun τ).2.2.2.2
  have hmin : ∀ τ, f xStar ≤ f (x τ) := fun τ => hxs.2 _ (hxC τ)
  refine ⟨(hprimal t ht).trans_eq (by rw [hK]; ring), ?_⟩
  set B := 4 * K / ((t : ℝ) + 3) with hB
  have hB0 : 0 ≤ B := by positivity
  by_contra hcon0
  have hcon : ∀ τ ≤ t, B < fderiv ℝ f (x τ) (x τ - v τ) := by
    intro τ hτ
    by_contra h
    push Not at h
    exact hcon0 ⟨τ, hτ, h.trans_eq (by rw [hB, hK]; ring)⟩
  rcases eq_or_lt_of_le hK0 with hK00 | hKpos
  · have h1 := (hfacts 1).2.1
    have h2 := hprimal 1 le_rfl
    have h3 := hcon 1 ht
    have h4 := hmin 2
    rw [← hD, ← hK, ← hK00] at h1
    rw [← hK00] at h2
    have hB00 : B = 0 := by rw [hB, ← hK00]; simp
    rw [hB00] at h3
    simp only [zero_div, mul_zero] at h1 h2
    linarith
  · set t0 := (t + 1) / 2 with ht0
    set n := t - t0 + 1 with hn
    have ht01 : 1 ≤ t0 := by omega
    have ht0t : t0 ≤ t := by omega
    have hprog : ∀ k < n, B ^ 2 / (2 * K) < f (x (t0 + k)) - f (x (t0 + k + 1)) := by
      intro k hk
      have hτ1 : 1 ≤ t0 + k := by omega
      have hg := hcon (t0 + k) (by omega)
      have hp := hprimal (t0 + k) hτ1
      have hle : 2 * K / (((t0 + k : ℕ) : ℝ) + 3) ≤ K / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (1 : ℝ) ≤ ((t0 + k : ℕ) : ℝ) := by exact_mod_cast hτ1
        nlinarith
      have hs1 := (hfacts (t0 + k)).2.1
      have hgK : fderiv ℝ f (x (t0 + k)) (x (t0 + k) - v (t0 + k)) ≤ K := by
        have := hmin (t0 + k + 1)
        rw [← hD, ← hK] at hs1
        linarith
      have hq := (hfacts (t0 + k)).2.2 hKpos hgK
      rw [← hD, ← hK] at hq
      have hsq : B ^ 2 < fderiv ℝ f (x (t0 + k)) (x (t0 + k) - v (t0 + k)) ^ 2 :=
        pow_lt_pow_left₀ hg hB0 two_ne_zero
      have : B ^ 2 / (2 * K) < fderiv ℝ f (x (t0 + k)) (x (t0 + k) - v (t0 + k)) ^ 2 / (2 * K) :=
        div_lt_div_of_pos_right hsq (by positivity)
      linarith
    have htel : ∀ m ≤ n, (m : ℝ) * (B ^ 2 / (2 * K)) ≤ f (x t0) - f (x (t0 + m)) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hprog m (by omega)
        rw [show t0 + (m + 1) = t0 + m + 1 by ring]
        push_cast
        linarith
    have hn1 : 1 ≤ n := by omega
    have hstrict : (n : ℝ) * (B ^ 2 / (2 * K)) < f (x t0) - f (x (t0 + n)) := by
      have h1 := hprog 0 (by omega)
      have h2 : ((n - 1 : ℕ) : ℝ) * (B ^ 2 / (2 * K)) ≤ f (x (t0 + 1)) - f (x (t0 + n)) := by
        have key : ∀ m ≤ n - 1, (m : ℝ) * (B ^ 2 / (2 * K)) ≤
            f (x (t0 + 1)) - f (x (t0 + 1 + m)) := by
          intro m
          induction m with
          | zero => intro _; simp
          | succ m ih =>
            intro hm
            have h3 := ih (by omega)
            have h4 := hprog (m + 1) (by omega)
            rw [show t0 + 1 + (m + 1) = t0 + 1 + m + 1 by ring]
            rw [show t0 + (m + 1) = t0 + 1 + m by ring] at h4
            push_cast
            linarith
        have := key (n - 1) le_rfl
        rwa [show t0 + 1 + (n - 1) = t0 + n by omega] at this
      have e : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub hn1]; ring
      rw [e]
      simp only [add_zero] at h1
      linarith
    have hup := hprimal t0 ht01
    have hlow := hmin (t0 + n)
    have hsplit := half_split t
    rw [← ht0, ← hn] at hsplit
    have eB : B ^ 2 / (2 * K) = 8 * K / ((t : ℝ) + 3) ^ 2 := by
      rw [hB]; field_simp; ring
    have hkey : 2 * K / ((t0 : ℝ) + 3) ≤ (n : ℝ) * (B ^ 2 / (2 * K)) := by
      rw [eB, div_le_iff₀ (by positivity)]
      have h3 : 0 < ((t : ℝ) + 3) ^ 2 := by positivity
      rw [show (n : ℝ) * (8 * K / ((t : ℝ) + 3) ^ 2) * ((t0 : ℝ) + 3) =
        2 * K * (4 * ((t0 : ℝ) + 3) * n / ((t : ℝ) + 3) ^ 2) by ring]
      have : 1 ≤ 4 * ((t0 : ℝ) + 3) * n / ((t : ℝ) + 3) ^ 2 := by
        rw [le_div_iff₀ h3]; linarith
      nlinarith
    linarith

theorem nonconvex_short_step_rate : NonconvexShortStepRate.{u} := by
  intro E _ _ C f L x v γ hC hCc hsm hx0 hrun xStar hxs t
  set D := Metric.diam C with hD
  set K : ℝ := L * D ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hbdd := hC.isBounded
  have hxC := iterates_mem hCc hx0 (fun t => ⟨(hrun t).1, (hrun t).2.2.1, (hrun t).2.2.2.1⟩)
  have hfacts := fun τ => step_facts (L := L) hbdd (hxC τ) (hrun τ).1 (hrun τ).2.1
    (hrun τ).2.2.2.2
  have hmin : ∀ τ, f xStar ≤ f (x τ) := fun τ => hxs.2 _ (hxC τ)
  set h0 := f (x 0) - f xStar with hh0
  have hh00 : 0 ≤ h0 := by linarith [hmin 0]
  set M := max (2 * h0) K with hM
  set r := Real.sqrt ((t : ℝ) + 1) with hr
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Real.one_le_sqrt.mpr (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)
  have hrr : r * r = (t : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  set B := M / r with hB
  have hM0 : 0 ≤ M := le_max_of_le_right hK0
  have hB0 : 0 ≤ B := div_nonneg hM0 (by linarith)
  by_contra hcon0
  have hcon : ∀ τ ≤ t, B < fderiv ℝ f (x τ) (x τ - v τ) := by
    intro τ hτ
    by_contra h
    push Not at h
    exact hcon0 ⟨τ, hτ, h⟩
  have htel : ∑ τ ∈ Finset.range (t + 1), (f (x τ) - f (x (τ + 1))) = f (x 0) - f (x (t + 1)) :=
    Finset.sum_range_sub' (fun τ => f (x τ)) (t + 1)
  have hlow := hmin (t + 1)
  have hcard : ((t : ℝ) + 1) = ((Finset.range (t + 1)).card : ℝ) := by simp
  rcases eq_or_lt_of_le hK0 with hK00 | hKpos
  · -- `K = 0`: every step gains more than `B`
    have hlt : ∑ τ ∈ Finset.range (t + 1), B <
        ∑ τ ∈ Finset.range (t + 1), (f (x τ) - f (x (τ + 1))) := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ (fun τ hτ => ?_)
      have h1 := (hfacts τ).2.1
      rw [← hD, ← hK, ← hK00] at h1
      have := hcon τ (by simpa [Nat.lt_succ_iff] using hτ)
      linarith
    rw [htel, Finset.sum_const, nsmul_eq_mul, ← hcard] at hlt
    have hM2 : M = 2 * h0 := by rw [hM, ← hK00]; exact max_eq_left (by linarith)
    have hBr : ((t : ℝ) + 1) * B = 2 * h0 * r := by
      rw [hB, hM2, ← hrr]; field_simp
    have : h0 ≤ 2 * h0 * r := by nlinarith
    linarith
  · set ψ := min (B ^ 2 / (2 * K)) (B / 2) with hψ
    have hlt : ∑ τ ∈ Finset.range (t + 1), ψ <
        ∑ τ ∈ Finset.range (t + 1), (f (x τ) - f (x (τ + 1))) := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ (fun τ hτ => ?_)
      have hg := hcon τ (by simpa [Nat.lt_succ_iff] using hτ)
      set g := fderiv ℝ f (x τ) (x τ - v τ) with hgdef
      have h1 := (hfacts τ).2.1
      rw [← hD, ← hK] at h1
      rcases le_or_gt g K with hgK | hgK
      · have h2 := (hfacts τ).2.2 hKpos hgK
        rw [← hD, ← hK] at h2
        have hsq : B ^ 2 < g ^ 2 := pow_lt_pow_left₀ hg hB0 two_ne_zero
        have : B ^ 2 / (2 * K) < g ^ 2 / (2 * K) := div_lt_div_of_pos_right hsq (by positivity)
        have := min_le_left (B ^ 2 / (2 * K)) (B / 2)
        linarith
      · have := min_le_right (B ^ 2 / (2 * K)) (B / 2)
        linarith
    rw [htel, Finset.sum_const, nsmul_eq_mul, ← hcard] at hlt
    have hA : h0 ≤ ((t : ℝ) + 1) * (B / 2) := by
      have e : ((t : ℝ) + 1) * (B / 2) = M * r / 2 := by
        rw [hB, ← hrr]; field_simp
      rw [e]
      have : 2 * h0 ≤ M := le_max_left _ _
      nlinarith
    have hBq : h0 ≤ ((t : ℝ) + 1) * (B ^ 2 / (2 * K)) := by
      have e : ((t : ℝ) + 1) * (B ^ 2 / (2 * K)) = M ^ 2 / (2 * K) := by
        rw [hB, ← hrr]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have h1 : 2 * h0 ≤ M := le_max_left _ _
      have h2 : K ≤ M := le_max_right _ _
      nlinarith
    have : h0 ≤ ((t : ℝ) + 1) * ψ := by
      rcases min_choice (B ^ 2 / (2 * K)) (B / 2) with h | h
      · rw [hψ, h]; exact hBq
      · rw [hψ, h]; exact hA
    linarith

end Proof

end Lemmata.CGBasics
