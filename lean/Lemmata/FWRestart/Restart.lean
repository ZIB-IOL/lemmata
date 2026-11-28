module

public import Lemmata.FWRestart.Fractional

@[expose] public section

/-!
# Scheduled restarts

Along scheduled restarts the invariant holds at every restart time, and the strong Wolfe gaps `W_k`
at the restart times are nonnegative with `W_{k+1} ≤ e^{-γ} W_k`. Before the burn-in condition
holds, every run takes at most `8 e^γ` iterations beyond the change in the size of the active set
(Proposition 4.2). After it, Proposition 4.1 and the strong Wolfe primal bound of Lemma 3.6 bound
run `k` by `K W_k^{r-2}`; telescoping `u_k = W_k^{r-2}`, which grows at least by the factor
`e^{γ(2-r)}` from one restart to the next, gives Theorem 5.1.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterations of Algorithm 1 keep the invariant, for a curvature bound `φ`. -/
theorem segment_inv_gen {V : Finset E} {f : E → ℝ} {φ : ℝ → ℝ} {ε : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hcurv : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
      ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + φ η)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀)) :
    ∀ n : ℕ, (∀ i < n, IsFAFWIter V f ε x S lam (t₀ + i)) →
      Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) := by
  intro n
  induction n with
  | zero => intro _; simpa using h0
  | succ n ih =>
    intro hit
    have hinv := ih (fun i hi => hit i (by omega))
    obtain ⟨v, hvV, hv, a, ha, -, hgap, hstep⟩ := hit n (by omega)
    have hgap' : 2 * (ε / 2) < fderiv ℝ f (x (t₀ + n)) (a - v) := by linarith
    exact (fafw_step_outcome_gen hconv hcurv hinv hvV hv ha hgap' hstep).1

/-- Iterations of Algorithm 1 keep the invariant. -/
theorem segment_inv {V : Finset E} {f : E → ℝ} {L : NNReal} {D ε : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀)) :
    ∀ n : ℕ, (∀ i < n, IsFAFWIter V f ε x S lam (t₀ + i)) →
      Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) :=
  segment_inv_gen hconv (smooth_curv hsm hD) h0

section Restart

variable {V : Finset E} {f : E → ℝ} {γ : ℝ} {x : ℕ → E} {S : ℕ → Finset E}
  {lam : ℕ → E → ℝ} {τ : ℕ → ℕ} {W : ℕ → ℝ}

theorem restart_iter (hrun : IsRestartRun V f γ x S lam τ W) (k : ℕ) :
    ∀ i < τ (k + 1) - τ k, IsFAFWIter V f (Real.exp (-γ) * W k) x S lam (τ k + i) := by
  intro i hi
  have hle := (hrun.2.2 k).1
  exact (hrun.2.2 k).2.2.2 (τ k + i) (by omega) (by omega)

theorem restart_inv_gen {φ : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hcurv : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
      ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + φ η)
    (hrun : IsRestartRun V f γ x S lam τ W) : ∀ k, Inv V (x (τ k)) (S (τ k)) (lam (τ k)) := by
  intro k
  induction k with
  | zero => rw [hrun.2.1]; exact inv_of_weighted hrun.1
  | succ k ih =>
    have hle := (hrun.2.2 k).1
    have := segment_inv_gen hconv hcurv ih (τ (k + 1) - τ k) (restart_iter hrun k)
    rwa [Nat.add_sub_cancel' hle] at this

theorem restart_inv {L : NNReal} {D : ℝ} (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    (hrun : IsRestartRun V f γ x S lam τ W) : ∀ k, Inv V (x (τ k)) (S (τ k)) (lam (τ k)) :=
  restart_inv_gen hconv (smooth_curv hsm hD) hrun

theorem restart_gap_nonneg (hinv : ∀ k, Inv V (x (τ k)) (S (τ k)) (lam (τ k)))
    (hrun : IsRestartRun V f γ x S lam τ W) (k : ℕ) : 0 ≤ W k := by
  obtain ⟨v, -, hv, a, -, haS, hW⟩ := (hrun.2.2 k).2.1
  rw [hW]
  exact gap_nonneg (hinv k) hv haS

theorem restart_chain (hrun : IsRestartRun V f γ x S lam τ W) (k : ℕ) :
    ∀ j : ℕ, W (k + j) ≤ Real.exp (-(γ * j)) * W k := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc W (k + (j + 1)) ≤ Real.exp (-γ) * W (k + j) := (hrun.2.2 (k + j)).2.2.1
      _ ≤ Real.exp (-γ) * (Real.exp (-(γ * j)) * W k) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (-(γ * ↑(j + 1))) * W k := by
          rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf

/-- A run that starts with gap `0` has no iterations. -/
theorem restart_zero (hrun : IsRestartRun V f γ x S lam τ W) {k : ℕ} (h0 : W k = 0) :
    τ (k + 1) = τ k := by
  have hle := (hrun.2.2 k).1
  by_contra hne
  have hlt : τ k < τ (k + 1) := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨v', hv'V, hv', a', ha', ha'S, hgap', -⟩ := (hrun.2.2 k).2.2.2 (τ k) le_rfl hlt
  obtain ⟨v, hvV, hv, a, ha, haS, hW⟩ := (hrun.2.2 k).2.1
  have e := gap_eq hvV hv'V hv hv' ha ha' haS ha'S
  rw [← e, ← hW, h0, mul_zero] at hgap'
  exact lt_irrefl _ hgap'

end Restart

namespace Proof

theorem burn_in : BurnIn.{u} := by
  intro E _ _ V f L D γ x S lam τ W hconv hsm hL hD0 hD hγ hrun hW0
  have hCpos : 0 < (L : ℝ) * D ^ 2 := by positivity
  have hinv := restart_inv hconv hsm hD hrun
  set N := ⌊Real.log (W 0 / (2 * (L * D ^ 2))) / γ⌋₊ with hN
  have hcondN : Real.exp (-γ) * W N / 2 ≤ L * D ^ 2 := by
    have hlt : Real.log (W 0 / (2 * (L * D ^ 2))) < γ * (N + 1) := by
      have := Nat.lt_floor_add_one (Real.log (W 0 / (2 * (L * D ^ 2))) / γ)
      rw [div_lt_iff₀ hγ] at this
      linarith
    have h1 : W 0 / (2 * (L * D ^ 2)) < Real.exp (γ * (N + 1)) := by
      rw [← Real.exp_log (by positivity : 0 < W 0 / (2 * (L * D ^ 2)))]
      exact Real.exp_lt_exp.mpr hlt
    have h2 : Real.exp (-γ) * W N ≤ Real.exp (-(γ * (N + 1))) * W 0 := by
      have := restart_chain hrun 0 N
      rw [zero_add] at this
      calc Real.exp (-γ) * W N ≤ Real.exp (-γ) * (Real.exp (-(γ * N)) * W 0) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = Real.exp (-(γ * (N + 1))) * W 0 := by rw [← mul_assoc, ← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(γ * (N + 1))) * W 0 < 2 * (L * D ^ 2) := by
      rw [Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
    linarith
  classical
  have hex : ∃ k, Real.exp (-γ) * W k / 2 ≤ L * D ^ 2 := ⟨N, hcondN⟩
  have hk₀N : Nat.find hex ≤ N := Nat.find_min' hex hcondN
  have hbefore : ∀ j < Nat.find hex, (L : ℝ) * D ^ 2 < Real.exp (-γ) * W j / 2 :=
    fun j hj => lt_of_not_ge (Nat.find_min hex hj)
  have hcount : ∀ k ≤ Nat.find hex,
      (τ k : ℝ) ≤ (S 0).card - (S (τ k)).card + 8 * Real.exp γ * k := by
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
        rw [hWeq]; exact primal_le_gap hconv hsm.1 (hinv k) hv haS hy
      have hle := (hrun.2.2 k).1
      have hb := (burn_in_run hconv hsm hD hWk hlarge.le (hinv k) hprimal (τ (k + 1) - τ k)
        (restart_iter hrun k)).2
      rw [Nat.add_sub_cancel' hle, Nat.cast_sub hle] at hb
      push_cast
      linarith
  exact ⟨Nat.find hex, hk₀N, Nat.find_spec hex, hcount _ le_rfl⟩

theorem restart_rate : RestartRate.{u} := by
  intro E _ _ V f L D c θ δ γ x S lam τ W xStar hconv hsm hD heb hc hθ hδ hsc hxs hγ hrun hburn R r
    K T
  have hinv := restart_inv hconv hsm hD hrun
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
  have hθ1 : 0 < 1 - θ := by linarith [hθ.2]
  have hr2 : r ≤ 2 := by
    show 1 / (1 - θ) ≤ 2
    rw [div_le_iff₀ hθ1]; linarith [hθ.2]
  have hμpos : 0 < (c / δ) ^ r := Real.rpow_pos_of_pos (div_pos hc hδ) r
  have hK0 : 0 ≤ K := by
    show 0 ≤ 16 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / δ) ^ r
    positivity
  have hprim : ∀ k, f (x (τ k)) - f xStar ≤ W k := fun k => by
    obtain ⟨v, -, hv, a, -, haS, hW⟩ := (hrun.2.2 k).2.1
    rw [hW]
    exact primal_le_gap hconv hsm.1 (hinv k) hv haS hxs.1
  -- the per-run bound (Proposition 4.1 with the strong Wolfe primal bound of Lemma 3.6)
  have hrunb : ∀ k, ((τ (k + 1) : ℝ) - τ k) ≤
      (S (τ k)).card - (S (τ (k + 1))).card + K * W k ^ (r - 2) := by
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
          (fun y _ => hsm.1 y) heb hc hθ hδ hsc hxs (hinv k).sub (hinv k).mem_convexHull ha haS
          hvV hv
        rw [← hW] at h1
        have h2 := hxs.2 y hy
        exact le_trans (by linarith) h1
      have hburnk : Real.exp (-γ) * W k / 2 ≤ L * D ^ 2 := by
        have := mul_le_mul_of_nonneg_left (hWle k) (Real.exp_pos (-γ)).le
        linarith
      have hb := (regular_run hconv hsm hD hpos hburnk (hinv k) hswp (τ (k + 1) - τ k)
        (restart_iter hrun k)).2
      rw [Nat.add_sub_cancel' hle, Nat.cast_sub hle] at hb
      exact hb
  -- telescoping the per-run bounds
  have htel : ∀ R' : ℕ, ((τ R' : ℝ) - ((S 0).card - (S (τ R')).card)) ≤
      K * ∑ k ∈ Finset.range R', W k ^ (r - 2) := by
    intro R'
    induction R' with
    | zero => rw [hrun.2.1]; simp
    | succ R' ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hrunb R'
      linarith
  have hT0 : 0 ≤ T := le_max_left _ _
  have hWR : W R ≤ Real.exp (-(γ * R)) * W 0 := by
    have := restart_chain hrun 0 R
    rwa [zero_add] at this
  refine ⟨fun hθlt => ?_, fun hθeq => ?_⟩
  · -- `θ < 1/2`, so `r < 2`
    have hr2' : r < 2 := by
      show 1 / (1 - θ) < 2
      rw [div_lt_iff₀ hθ1]; linarith
    set ρ := Real.exp (γ * (2 - r)) with hρdef
    have hρ1 : 1 < ρ := Real.one_lt_exp_iff.mpr (mul_pos hγ (by linarith))
    have hC0 : 0 ≤ (ρ - 1) / (K * W 0 ^ (r - 2)) :=
      div_nonneg (by linarith) (mul_nonneg hK0 (Real.rpow_nonneg (hWnn 0) _))
    have hbase : 1 ≤ 1 + T * ((ρ - 1) / (K * W 0 ^ (r - 2))) := by
      have := mul_nonneg hT0 hC0
      linarith
    rcases eq_or_lt_of_le (hWnn R) with hR0 | hRpos
    · calc f (x (τ R)) - f xStar ≤ W R := hprim R
        _ = 0 := hR0.symm
        _ ≤ _ := div_nonneg (hWnn 0) (Real.rpow_nonneg (by linarith) _)
    have hWpos : ∀ k ≤ R, 0 < W k := by
      intro k hk
      have := restart_chain hrun k (R - k)
      rw [Nat.add_sub_cancel' hk] at this
      by_contra hneg
      push Not at hneg
      have : Real.exp (-(γ * ↑(R - k))) * W k ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
      linarith
    -- `u_k = W_k^{r-2}` grows at least by the factor `ρ`
    have hgrow : ∀ k < R, ρ * W k ^ (r - 2) ≤ W (k + 1) ^ (r - 2) := by
      intro k hk
      have h1 : (Real.exp (-γ) * W k) ^ (r - 2) ≤ W (k + 1) ^ (r - 2) :=
        Real.rpow_le_rpow_of_nonpos (hWpos (k + 1) hk) (hWstep k) (by linarith)
      rw [Real.mul_rpow (Real.exp_pos _).le (hWnn k), ← Real.exp_mul] at h1
      have e : -γ * (r - 2) = γ * (2 - r) := by ring
      rwa [e] at h1
    have htel2 : ∀ R' ≤ R, (ρ - 1) * ∑ k ∈ Finset.range R', W k ^ (r - 2) ≤
        W R' ^ (r - 2) - W 0 ^ (r - 2) := by
      intro R' hR'
      induction R' with
      | zero => simp
      | succ R' ih =>
        rw [Finset.sum_range_succ, mul_add]
        have h1 := ih (by omega)
        have h2 := hgrow R' (by omega)
        linarith
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range R, W k ^ (r - 2) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hWnn k) _
    have hW0pos : 0 < W 0 := hWpos 0 (Nat.zero_le _)
    have hCpos : 0 < (L : ℝ) * D ^ 2 := by
      have := mul_pos (Real.exp_pos (-γ)) hW0pos
      linarith
    have hKpos : 0 < K := by
      show 0 < 16 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / δ) ^ r
      have := Real.exp_pos (2 * γ)
      exact mul_pos (mul_pos (by positivity) hCpos) hμpos
    have hu0 : 0 < W 0 ^ (r - 2) := Real.rpow_pos_of_pos hW0pos _
    have hkey : W 0 ^ (r - 2) * (1 + T * ((ρ - 1) / (K * W 0 ^ (r - 2)))) ≤ W R ^ (r - 2) := by
      have e : W 0 ^ (r - 2) * (1 + T * ((ρ - 1) / (K * W 0 ^ (r - 2)))) =
          W 0 ^ (r - 2) + (ρ - 1) * T / K := by
        field_simp
      rw [e]
      have h2 := htel2 R le_rfl
      have h3 : (ρ - 1) * T / K ≤ (ρ - 1) * ∑ k ∈ Finset.range R, W k ^ (r - 2) := by
        rw [div_le_iff₀ hKpos]
        have hTle : T ≤ K * ∑ k ∈ Finset.range R, W k ^ (r - 2) :=
          max_le (mul_nonneg hK0 hsum0) (htel R)
        have := mul_le_mul_of_nonneg_left hTle (by linarith : (0 : ℝ) ≤ ρ - 1)
        linarith
      linarith
    -- invert with the negative exponent `1/(r - 2)`
    have hne : r - 2 ≠ 0 := by linarith
    have hneg : (r - 2)⁻¹ ≤ 0 := inv_nonpos.mpr (by linarith)
    have hlhs : 0 < W 0 ^ (r - 2) * (1 + T * ((ρ - 1) / (K * W 0 ^ (r - 2)))) :=
      mul_pos hu0 (by linarith)
    have hfin := Real.rpow_le_rpow_of_nonpos hlhs hkey hneg
    rw [Real.rpow_rpow_inv (hWnn R) hne, Real.mul_rpow hu0.le (by linarith),
      Real.rpow_rpow_inv (hWnn 0) hne] at hfin
    have e2 : (r - 2)⁻¹ = -(1 / (2 - r)) := by
      field_simp
      ring_nf
    rw [e2, Real.rpow_neg (by linarith), ← div_eq_mul_inv] at hfin
    exact (hprim R).trans hfin
  · -- `θ = 1/2`, so `r = 2`
    have hr : r = 2 := by
      show 1 / (1 - θ) = 2
      rw [hθeq]; norm_num
    have hsum : ∑ k ∈ Finset.range R, W k ^ (r - 2) = R := by
      rw [hr, sub_self]
      simp
    have hTle : T ≤ K * R := by
      have := htel R
      rw [hsum] at this
      exact max_le (mul_nonneg hK0 (Nat.cast_nonneg R)) this
    calc f (x (τ R)) - f xStar ≤ W R := hprim R
      _ ≤ Real.exp (-(γ * R)) * W 0 := hWR
      _ ≤ W 0 * Real.exp (-(γ * T / K)) := by
        rcases eq_or_lt_of_le (hWnn 0) with h0 | hpos
        · rw [← h0]; simp
        · have hCpos : 0 < (L : ℝ) * D ^ 2 := by
            have := mul_pos (Real.exp_pos (-γ)) hpos
            linarith
          have hKpos : 0 < K := by
            show 0 < 16 * Real.exp (2 * γ) * ((L : ℝ) * D ^ 2) * (c / δ) ^ r
            have := Real.exp_pos (2 * γ)
            exact mul_pos (mul_pos (by positivity) hCpos) hμpos
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ hpos.le
          apply Real.exp_le_exp.mpr
          have h1 : T / K ≤ R := by rw [div_le_iff₀ hKpos]; linarith
          have h2 : γ * T / K ≤ γ * R := by
            rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 hγ.le
          linarith

end Proof

end Lemmata.FWRestart
