module

public import Lemmata.FWRestart.Restart

@[expose] public section

/-!
# Hölder smoothness and robustness in `γ`

With Hölder curvature `C η^s/s` in place of `L D² η²/2`, the full steps of Algorithm 1 decrease `f`
by `η G - C η^s/s` for every `η ∈ [0, 1]`; at `η₀ = (G/C)^{1/(s-1)}` this is `(1 - 1/s) G η₀`,
which gives Proposition 6.1, and at `η = 1` in the burn-in regime it is at least `(1 - 1/s) G`,
which gives Proposition 6.3. Telescoping the per-run bounds `K W_k^{-a}` of scheduled restarts,
with `W_k^{-a}` growing by the factor `e^{γ a}` from one restart to the next, gives Theorem 6.2.
Proposition 5.3 compares the bounds of Theorem 5.1 for different `γ`.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The algebra of Proposition 6.1. -/
theorem holder_algebra {γ w₀ μ r C s : ℝ} (hw₀ : 0 < w₀) (hC : 0 < C) (hs : 1 < s) :
    2 * (μ * w₀ ^ r) / ((s - 1) / s * (Real.exp (-γ) * w₀ / 2) *
      ((Real.exp (-γ) * w₀ / 2) / C) ^ (1 / (s - 1))) =
      2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * Real.exp (s / (s - 1) * γ) * μ *
        C ^ (1 / (s - 1)) * w₀ ^ (r - s / (s - 1)) := by
  set p := 1 / (s - 1) with hp
  have hs1 : 0 < s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hq : s / (s - 1) = 1 + p := by rw [hp]; field_simp; ring
  have hG : 0 < Real.exp (-γ) * w₀ / 2 := by positivity
  have h1 : (Real.exp (-γ) * w₀ / 2) * ((Real.exp (-γ) * w₀ / 2) / C) ^ p =
      w₀ ^ (1 + p) / (Real.exp ((1 + p) * γ) * (2 * 2 ^ p) * C ^ p) := by
    rw [Real.div_rpow hG.le hC.le, ← mul_div_assoc,
      ← Real.rpow_one_add' hG.le (by positivity : (1 : ℝ) + p ≠ 0),
      Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity) hw₀.le,
      ← Real.exp_mul, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have e : Real.exp (-γ * (1 + p)) = (Real.exp ((1 + p) * γ))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [e]
    field_simp
  have h2 : (2 : ℝ) ^ (1 + s / (s - 1)) = 4 * 2 ^ p := by
    rw [hq, show (1 : ℝ) + (1 + p) = 2 + p by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h4 : w₀ ^ (r - s / (s - 1)) = w₀ ^ r / w₀ ^ (1 + p) := by rw [hq, Real.rpow_sub hw₀]
  have h5 : Real.exp (s / (s - 1) * γ) = Real.exp ((1 + p) * γ) := by rw [hq]
  rw [mul_assoc ((s - 1) / s), h1, h2, h4, h5]
  have hEx : 0 < Real.exp ((1 + p) * γ) := Real.exp_pos _
  have hTp : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hCp : 0 < C ^ p := Real.rpow_pos_of_pos hC p
  have hWq : 0 < w₀ ^ (1 + p) := Real.rpow_pos_of_pos hw₀ _
  generalize Real.exp ((1 + p) * γ) = Ex at hEx ⊢
  generalize (2 : ℝ) ^ p = Tp at hTp ⊢
  generalize C ^ p = Cp at hCp ⊢
  generalize w₀ ^ (1 + p) = Wq at hWq ⊢
  generalize w₀ ^ r = Wr
  field_simp
  ring

namespace Proof

/-- Proposition 6.1 for a run of Algorithm 1 started at iteration `t₀`. -/
theorem holder_run {V : Finset E} {f : E → ℝ} {C s γ w₀ μ r : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hcurv : IsHolderCurvature V f C s) (hs : 1 < s)
    (hw₀ : 0 < w₀) (hburn : Real.exp (-γ) * w₀ / 2 ≤ C)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀))
    (hprimal : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x t₀) - f y ≤ μ * w₀ ^ r) (n : ℕ)
    (hit : ∀ i < n, IsFAFWIter V f (Real.exp (-γ) * w₀) x S lam (t₀ + i)) :
    Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
      (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card + 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) *
        Real.exp (s / (s - 1) * γ) * μ * C ^ (1 / (s - 1)) * w₀ ^ (r - s / (s - 1)) := by
  set G := Real.exp (-γ) * w₀ / 2 with hGdef
  have hG : 0 < G := by positivity
  have hC : 0 < C := lt_of_lt_of_le hG hburn
  have hs1 : 0 < s - 1 := by linarith
  set p := 1 / (s - 1) with hp
  have hp0 : 0 < p := by positivity
  set η₀ := (G / C) ^ p with hη₀def
  have hGC : 0 ≤ G / C := div_nonneg hG.le hC.le
  have hη₀ : η₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg hGC p, Real.rpow_le_one hGC ((div_le_one hC).mpr hburn) hp0.le⟩
  have hη₀pos : 0 < η₀ := Real.rpow_pos_of_pos (div_pos hG hC) p
  have hηs : η₀ ^ s = η₀ * (G / C) := by
    rw [hη₀def, ← Real.rpow_mul hGC, show p * s = 1 + p by rw [hp]; field_simp; ring,
      Real.rpow_one_add' hGC (by positivity), mul_comm]
  set P := (s - 1) / s * G * η₀ with hPdef
  have hP : 0 < P := by positivity
  have hPle : P ≤ η₀ * (Real.exp (-γ) * w₀ / 2) - C * η₀ ^ s / s := by
    rw [hηs, ← hGdef]
    have : C * (η₀ * (G / C)) = G * η₀ := by field_simp
    rw [this, hPdef]
    have hs0 : 0 < s := by linarith
    field_simp
    ring_nf
    exact le_refl _
  obtain ⟨hinv, hb⟩ := segment_bound_gen (φ := fun η => C * η ^ s / s) hconv hcurv hη₀ hP hPle h0
    n hit
  refine ⟨hinv, ?_⟩
  have hfT := hprimal (x (t₀ + n)) (mem_hull_of_inv hinv)
  have hstep : 2 * (f (x t₀) - f (x (t₀ + n))) / P ≤ 2 * (μ * w₀ ^ r) / P :=
    div_le_div_of_nonneg_right (by linarith) hP.le
  rw [hPdef, mul_assoc, hGdef, hη₀def, hp, ← mul_assoc, holder_algebra hw₀ hC hs] at hstep
  linarith

theorem holder_complexity : HolderComplexity.{u} := by
  intro E _ _ V f C s γ w₀ μ r x S lam T hconv _ hcurv hs hw₀ hburn hrun hprimal
  obtain ⟨hst, hit⟩ := hrun
  have h := (holder_run hconv hcurv hs hw₀ hburn (t₀ := 0) (by simpa using inv_of_weighted hst)
    (by simpa using hprimal) T (fun i hi => by simpa using hit i hi)).2
  simpa using h

/-- One run of Algorithm 1 in the burn-in regime `C ≤ e^{-γ} w₀/2` under Hölder smoothness. -/
theorem holder_burn_run {V : Finset E} {f : E → ℝ} {C s γ w₀ : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hcurv : IsHolderCurvature V f C s) (hs : 1 < s)
    (hw₀ : 0 < w₀) (hlarge : C ≤ Real.exp (-γ) * w₀ / 2)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀))
    (hprimal : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x t₀) - f y ≤ w₀) (n : ℕ)
    (hit : ∀ i < n, IsFAFWIter V f (Real.exp (-γ) * w₀) x S lam (t₀ + i)) :
    Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
      (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card + 4 * (s / (s - 1)) * Real.exp γ := by
  set G := Real.exp (-γ) * w₀ / 2 with hGdef
  have hG : 0 < G := by positivity
  have hs1 : 0 < s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hP : 0 < (s - 1) / s * G := by positivity
  have hPle : (s - 1) / s * G ≤ 1 * (Real.exp (-γ) * w₀ / 2) - C * (1 : ℝ) ^ s / s := by
    rw [Real.one_rpow, mul_one, one_mul, ← hGdef]
    have h1 : C / s ≤ G / s := div_le_div_of_nonneg_right hlarge hs0.le
    have e : (s - 1) / s * G = G - G / s := by field_simp
    rw [e]
    linarith
  obtain ⟨hinv, hb⟩ := segment_bound_gen (φ := fun η => C * η ^ s / s) hconv hcurv
    ⟨zero_le_one, le_rfl⟩ hP hPle h0 n hit
  refine ⟨hinv, ?_⟩
  have hf := hprimal (x (t₀ + n)) (mem_hull_of_inv hinv)
  have h1 : 2 * (f (x t₀) - f (x (t₀ + n))) / ((s - 1) / s * G) ≤ 2 * w₀ / ((s - 1) / s * G) :=
    div_le_div_of_nonneg_right (by linarith) hP.le
  have h2 : 2 * w₀ / ((s - 1) / s * G) = 4 * (s / (s - 1)) * Real.exp γ := by
    rw [hGdef, Real.exp_neg]
    field_simp
    ring
  linarith

theorem holder_burn_in : HolderBurnIn.{u} := by
  intro E _ _ V f C s γ x S lam τ W hconv hdiff hcurv hs hC hγ hrun hW0
  have hinv := restart_inv_gen (φ := fun η => C * η ^ s / s) hconv hcurv hrun
  set N := ⌊Real.log (W 0 / (2 * C)) / γ⌋₊ with hN
  have hcondN : Real.exp (-γ) * W N / 2 ≤ C := by
    have hlt : Real.log (W 0 / (2 * C)) < γ * (N + 1) := by
      have := Nat.lt_floor_add_one (Real.log (W 0 / (2 * C)) / γ)
      rw [div_lt_iff₀ hγ] at this
      linarith
    have h1 : W 0 / (2 * C) < Real.exp (γ * (N + 1)) := by
      rw [← Real.exp_log (by positivity : 0 < W 0 / (2 * C))]
      exact Real.exp_lt_exp.mpr hlt
    have h2 : Real.exp (-γ) * W N ≤ Real.exp (-(γ * (N + 1))) * W 0 := by
      have := restart_chain hrun 0 N
      rw [zero_add] at this
      calc Real.exp (-γ) * W N ≤ Real.exp (-γ) * (Real.exp (-(γ * N)) * W 0) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = Real.exp (-(γ * (N + 1))) * W 0 := by rw [← mul_assoc, ← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(γ * (N + 1))) * W 0 < 2 * C := by
      rw [Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
    linarith
  classical
  have hex : ∃ k, Real.exp (-γ) * W k / 2 ≤ C := ⟨N, hcondN⟩
  have hk₀N : Nat.find hex ≤ N := Nat.find_min' hex hcondN
  have hbefore : ∀ j < Nat.find hex, C < Real.exp (-γ) * W j / 2 :=
    fun j hj => lt_of_not_ge (Nat.find_min hex hj)
  have hcount : ∀ k ≤ Nat.find hex,
      (τ k : ℝ) ≤ (S 0).card - (S (τ k)).card + 4 * (s / (s - 1)) * Real.exp γ * k := by
    intro k
    induction k with
    | zero => intro _; rw [hrun.2.1]; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hlarge := hbefore k (by omega)
      have hWk : 0 < W k := by
        have h' : 0 < Real.exp (-γ) * W k := by linarith
        exact pos_of_mul_pos_right h' (Real.exp_pos _).le
      obtain ⟨v, -, hv, a, -, haS, hWeq⟩ := (hrun.2.2 k).2.1
      have hprimal : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x (τ k)) - f y ≤ W k := fun y hy => by
        rw [hWeq]; exact primal_le_gap hconv hdiff (hinv k) hv haS hy
      have hle := (hrun.2.2 k).1
      have hb := (holder_burn_run hconv hcurv hs hWk hlarge.le (hinv k) hprimal
        (τ (k + 1) - τ k) (restart_iter hrun k)).2
      rw [Nat.add_sub_cancel' hle, Nat.cast_sub hle] at hb
      push_cast
      linarith
  exact ⟨Nat.find hex, hk₀N, Nat.find_spec hex, hcount _ le_rfl⟩

end Proof

/-- Telescoping the per-run bounds of scheduled restarts: if `W_{k+1} ≤ e^{-γ} W_k` and the total
count `T` is at most `K ∑_{k<R} W_k^{-a}`, then
`W_R ≤ W₀/(1 + T₊ (e^{γa} - 1)/(K W₀^{-a}))^{1/a}`. -/
theorem rate_of_telescope {W : ℕ → ℝ} {γ a K T : ℝ} (R : ℕ) (hγ : 0 < γ) (ha : 0 < a)
    (hWnn : ∀ k, 0 ≤ W k) (hWstep : ∀ k, W (k + 1) ≤ Real.exp (-γ) * W k) (hK0 : 0 ≤ K)
    (hK : 0 < W 0 → 0 < K) (hT : T ≤ K * ∑ k ∈ Finset.range R, W k ^ (-a)) :
    W R ≤ W 0 / (1 + max 0 T * ((Real.exp (γ * a) - 1) / (K * W 0 ^ (-a)))) ^ (1 / a) := by
  set ρ := Real.exp (γ * a) with hρdef
  have hρ1 : 1 < ρ := Real.one_lt_exp_iff.mpr (mul_pos hγ ha)
  have hT0 : 0 ≤ max 0 T := le_max_left _ _
  have hC0 : 0 ≤ (ρ - 1) / (K * W 0 ^ (-a)) :=
    div_nonneg (by linarith) (mul_nonneg hK0 (Real.rpow_nonneg (hWnn 0) _))
  have hbase : 1 ≤ 1 + max 0 T * ((ρ - 1) / (K * W 0 ^ (-a))) := by
    have := mul_nonneg hT0 hC0
    linarith
  have hchain : ∀ k j : ℕ, W (k + j) ≤ Real.exp (-(γ * j)) * W k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      calc W (k + (j + 1)) ≤ Real.exp (-γ) * W (k + j) := hWstep (k + j)
        _ ≤ Real.exp (-γ) * (Real.exp (-(γ * j)) * W k) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (-(γ * ↑(j + 1))) * W k := by
            rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf
  rcases eq_or_lt_of_le (hWnn R) with hR0 | hRpos
  · rw [← hR0]
    exact div_nonneg (hWnn 0) (Real.rpow_nonneg (by linarith) _)
  have hWpos : ∀ k ≤ R, 0 < W k := by
    intro k hk
    have := hchain k (R - k)
    rw [Nat.add_sub_cancel' hk] at this
    by_contra hneg
    push Not at hneg
    have : Real.exp (-(γ * ↑(R - k))) * W k ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
    linarith
  have hgrow : ∀ k < R, ρ * W k ^ (-a) ≤ W (k + 1) ^ (-a) := by
    intro k hk
    have h1 : (Real.exp (-γ) * W k) ^ (-a) ≤ W (k + 1) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (hWpos (k + 1) hk) (hWstep k) (by linarith)
    rw [Real.mul_rpow (Real.exp_pos _).le (hWnn k), ← Real.exp_mul] at h1
    have e : -γ * -a = γ * a := by ring
    rwa [e] at h1
  have htel : ∀ R' ≤ R, (ρ - 1) * ∑ k ∈ Finset.range R', W k ^ (-a) ≤
      W R' ^ (-a) - W 0 ^ (-a) := by
    intro R' hR'
    induction R' with
    | zero => simp
    | succ R' ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h1 := ih (by omega)
      have h2 := hgrow R' (by omega)
      linarith
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range R, W k ^ (-a) :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hWnn k) _
  have hW0pos : 0 < W 0 := hWpos 0 (Nat.zero_le _)
  have hKpos : 0 < K := hK hW0pos
  have hu0 : 0 < W 0 ^ (-a) := Real.rpow_pos_of_pos hW0pos _
  have hkey : W 0 ^ (-a) * (1 + max 0 T * ((ρ - 1) / (K * W 0 ^ (-a)))) ≤ W R ^ (-a) := by
    have e : W 0 ^ (-a) * (1 + max 0 T * ((ρ - 1) / (K * W 0 ^ (-a)))) =
        W 0 ^ (-a) + (ρ - 1) * max 0 T / K := by
      field_simp
    rw [e]
    have h2 := htel R le_rfl
    have h3 : (ρ - 1) * max 0 T / K ≤ (ρ - 1) * ∑ k ∈ Finset.range R, W k ^ (-a) := by
      rw [div_le_iff₀ hKpos]
      have hTle : max 0 T ≤ K * ∑ k ∈ Finset.range R, W k ^ (-a) :=
        max_le (mul_nonneg hK0 hsum0) hT
      have := mul_le_mul_of_nonneg_left hTle (by linarith : (0 : ℝ) ≤ ρ - 1)
      linarith
    linarith
  have hne : -a ≠ 0 := by linarith
  have hneg : (-a)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith)
  have hlhs : 0 < W 0 ^ (-a) * (1 + max 0 T * ((ρ - 1) / (K * W 0 ^ (-a)))) :=
    mul_pos hu0 (by linarith)
  have hfin := Real.rpow_le_rpow_of_nonpos hlhs hkey hneg
  rw [Real.rpow_rpow_inv (hWnn R) hne, Real.mul_rpow hu0.le (by linarith),
    Real.rpow_rpow_inv (hWnn 0) hne] at hfin
  have e2 : (-a)⁻¹ = -(1 / a) := by rw [inv_neg, one_div]
  rw [e2, Real.rpow_neg (by linarith), ← div_eq_mul_inv] at hfin
  exact hfin

namespace Proof

theorem holder_restart_rate : HolderRestartRate.{u} := by
  intro E _ _ V f C s c θ δ γ x S lam τ W xStar hconv hdiff hcurv hs heb hc hθ hrs hδ hsc hxs hγ
    hrun hburn R r K T
  have hinv := restart_inv_gen (φ := fun η => C * η ^ s / s) hconv hcurv hrun
  have hWnn : ∀ k, 0 ≤ W k := restart_gap_nonneg hinv hrun
  have hWstep : ∀ k, W (k + 1) ≤ Real.exp (-γ) * W k := fun k => (hrun.2.2 k).2.2.1
  have hexp1 : Real.exp (-γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hWle : ∀ k, W k ≤ W 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have := hWstep k
      have := hWnn k
      nlinarith
  have hs1 : 0 < s - 1 := by linarith
  have hμpos : 0 < (c / δ) ^ r := Real.rpow_pos_of_pos (div_pos hc hδ) r
  have hprim : ∀ k, f (x (τ k)) - f xStar ≤ W k := fun k => by
    obtain ⟨v, -, hv, a, -, haS, hW⟩ := (hrun.2.2 k).2.1
    rw [hW]
    exact primal_le_gap hconv hdiff (hinv k) hv haS hxs.1
  -- `C ≥ 0` from the burn-in condition
  have hC0 : 0 ≤ C := le_trans (by have := hWnn 0; positivity) hburn
  have hK0 : 0 ≤ K := by
    show 0 ≤ 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * (c / δ) ^ r * C ^ (1 / (s - 1)) *
      Real.exp (s / (s - 1) * γ)
    have := Real.rpow_nonneg hC0 (1 / (s - 1))
    positivity
  -- the per-run bound
  have hrunb : ∀ k, ((τ (k + 1) : ℝ) - τ k) ≤
      (S (τ k)).card - (S (τ (k + 1))).card + K * W k ^ (-(s / (s - 1) - r)) := by
    intro k
    have hle := (hrun.2.2 k).1
    rcases eq_or_lt_of_le (hWnn k) with h0 | hpos
    · rw [restart_zero hrun h0.symm]
      simp only [sub_self, zero_add]
      exact mul_nonneg hK0 (Real.rpow_nonneg (hWnn k) _)
    · obtain ⟨v, hvV, hv, a, ha, haS, hW⟩ := (hrun.2.2 k).2.1
      have hswp : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x (τ k)) - f y ≤ (c / δ) ^ r * W k ^ r := by
        intro y hy
        have h1 := heb_strong_wolfe (hconv.subset (Set.subset_univ _) (convex_convexHull ℝ _))
          (fun y _ => hdiff y) heb hc hθ hδ hsc hxs (hinv k).sub (hinv k).mem_convexHull ha haS
          hvV hv
        rw [← hW] at h1
        have h2 := hxs.2 y hy
        exact le_trans (by linarith) h1
      have hburnk : Real.exp (-γ) * W k / 2 ≤ C := by
        have := mul_le_mul_of_nonneg_left (hWle k) (Real.exp_pos (-γ)).le
        linarith
      have hb := (holder_run hconv hcurv hs hpos hburnk (hinv k) hswp (τ (k + 1) - τ k)
        (restart_iter hrun k)).2
      rw [Nat.add_sub_cancel' hle, Nat.cast_sub hle] at hb
      have e : 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * Real.exp (s / (s - 1) * γ) *
          (c / δ) ^ r * C ^ (1 / (s - 1)) * W k ^ (r - s / (s - 1)) =
          K * W k ^ (-(s / (s - 1) - r)) := by
        rw [show -(s / (s - 1) - r) = r - s / (s - 1) by ring]
        show _ = 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * (c / δ) ^ r * C ^ (1 / (s - 1)) *
          Real.exp (s / (s - 1) * γ) * W k ^ (r - s / (s - 1))
        ring
      linarith
  have htel : ∀ R' : ℕ, ((τ R' : ℝ) - ((S 0).card - (S (τ R')).card)) ≤
      K * ∑ k ∈ Finset.range R', W k ^ (-(s / (s - 1) - r)) := by
    intro R'
    induction R' with
    | zero => rw [hrun.2.1]; simp
    | succ R' ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hrunb R'
      linarith
  have hKpos : 0 < W 0 → 0 < K := by
    intro hW0
    have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hburn
    show 0 < 2 ^ (1 + s / (s - 1)) * (s / (s - 1)) * (c / δ) ^ r * C ^ (1 / (s - 1)) *
      Real.exp (s / (s - 1) * γ)
    have := Real.rpow_pos_of_pos hCpos (1 / (s - 1))
    positivity
  have ha : 0 < s / (s - 1) - r := by linarith [hrs]
  have hrate := rate_of_telescope R hγ ha hWnn hWstep hK0 hKpos (htel R)
  have e3 : W 0 ^ (-(s / (s - 1) - r)) = W 0 ^ (r - s / (s - 1)) := by ring_nf
  rw [e3] at hrate
  exact (hprim R).trans hrate

/-- Comparing two bounds `W₀/(1 + T c)`. -/
theorem bound_cmp {W₀ T κ c₁ cγ : ℝ} (hW₀ : 0 < W₀) (hT : 0 ≤ T) (hc₁ : 0 ≤ c₁) (hcγ : 0 ≤ cγ)
    (hκ1 : 1 ≤ κ) (hcmp : cγ ≤ κ * c₁) : W₀ / (1 + T * c₁) ≤ κ * (W₀ / (1 + T * cγ)) := by
  have hd1 : 0 < 1 + T * c₁ := by have := mul_nonneg hT hc₁; linarith
  have hd2 : 0 < 1 + T * cγ := by have := mul_nonneg hT hcγ; linarith
  have h1 : 1 + T * cγ ≤ κ * (1 + T * c₁) := by
    have := mul_le_mul_of_nonneg_left hcmp hT
    nlinarith
  rw [div_le_iff₀ hd1]
  calc W₀ = W₀ / (1 + T * cγ) * (1 + T * cγ) := by field_simp
    _ ≤ W₀ / (1 + T * cγ) * (κ * (1 + T * c₁)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hW₀.le hd2.le)
    _ = κ * (W₀ / (1 + T * cγ)) * (1 + T * c₁) := by ring

theorem robust_gamma : RobustGamma := by
  intro K₀ W₀ T γ hK₀ hW₀ hT hγ
  refine ⟨?_, ?_⟩
  · -- `r = 1`: `(e^γ - 1)/e^{2γ} ≤ 1/4 = κ (e^{1/2} - 1)/e`
    have hsq : Real.exp (1 / 2) = Real.sqrt (Real.exp 1) := by
      rw [← Real.exp_half]
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hs0 : 1 < Real.sqrt (Real.exp 1) := by
      rw [← hsq]; exact Real.one_lt_exp_iff.mpr (by norm_num)
    have hss : Real.sqrt (Real.exp 1) * Real.sqrt (Real.exp 1) = Real.exp 1 :=
      Real.mul_self_sqrt he.le
    have hden : 0 < 4 * (Real.sqrt (Real.exp 1) - 1) := by linarith
    have hW : W₀ ^ ((1 : ℝ) - 2) = W₀⁻¹ := by
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    have he2 : Real.exp (2 * (1 / 2)) = Real.exp 1 := by norm_num
    rw [hW, he2, hsq]
    refine bound_cmp hW₀ hT ?_ ?_ ?_ ?_
    · exact div_nonneg (by linarith) (by positivity)
    · exact div_nonneg (by linarith [Real.one_lt_exp_iff.mpr hγ]) (by positivity)
    · rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg (Real.sqrt (Real.exp 1) - 2)]
    · have hquart : (Real.exp γ - 1) / Real.exp (2 * γ) ≤ 1 / 4 := by
        have hE := Real.exp_pos γ
        rw [show 2 * γ = γ + γ by ring, Real.exp_add, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.exp γ - 2)]
      have e1 : (Real.exp γ - 1) / (Real.exp (2 * γ) * K₀ * W₀⁻¹) =
          (Real.exp γ - 1) / Real.exp (2 * γ) * (W₀ / K₀) := by
        field_simp
      have e2 : Real.exp 1 / (4 * (Real.sqrt (Real.exp 1) - 1)) *
          ((Real.sqrt (Real.exp 1) - 1) / (Real.exp 1 * K₀ * W₀⁻¹)) = 1 / 4 * (W₀ / K₀) := by
        field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hquart (by positivity)
  · -- `r = 2`: `γ e^{-2γ} ≤ e^{-1}/2`
    apply mul_le_mul_of_nonneg_left _ hW₀.le
    apply Real.exp_le_exp.mpr
    have h1 : 2 * γ ≤ Real.exp (2 * γ - 1) := by
      have := Real.add_one_le_exp (2 * γ - 1)
      linarith
    have he1 : Real.exp (2 * γ - 1) = Real.exp (2 * γ) / Real.exp 1 := by
      rw [Real.exp_sub]
    rw [he1, le_div_iff₀ (Real.exp_pos 1)] at h1
    have he2 : Real.exp (2 * (1 / 2)) = Real.exp 1 := by norm_num
    rw [he2, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    have hT' : 0 ≤ T * K₀ := mul_nonneg hT hK₀.le
    nlinarith [Real.exp_pos (2 * γ), Real.exp_pos 1]

end Proof

end Lemmata.FWRestart
