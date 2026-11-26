module

public import Lemmata.FrankWolfe.Proof.Calculus
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# The `O(1/t)` rate of the Frank–Wolfe algorithm

The iterates stay feasible; one step from `x` toward the atom contracts the primal gap,
`h⁺ ≤ (1 - γ) h + γ² L D² / 2`; short steps and exact line search do at least as well as any
`γ ∈ [0, 1]`; and the recursion with `γ_t = 2/(t + 2)` gives `h_t ≤ 2 L D² / (t + 2)`.
-/

namespace Lemmata.FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Frank–Wolfe iterates stay in a convex `C` when every step size at points of `C` is in `[0, 1]`. -/
theorem fwIterates_mem {C : Set E} (hC : Convex ℝ C) {lmo : StrongDual ℝ E → E}
    (hlmo : ∀ g, lmo g ∈ C) (f' : E → StrongDual ℝ E) {step : ℕ → E → ℝ}
    (hstep : ∀ t, ∀ x ∈ C, step t x ∈ Set.Icc (0 : ℝ) 1) {x₀ : E} (hx₀ : x₀ ∈ C) :
    ∀ t, fwIterates lmo f' step x₀ t ∈ C := by
  intro t
  induction t with
  | zero => exact hx₀
  | succ t ih => exact hC.add_smul_sub_mem ih (hlmo _) (hstep t _ ih)

namespace StandingAssumptions

variable {C : Set E} {lmo : StrongDual ℝ E → E} {f : E → ℝ} {L : NNReal}

theorem isCompact (h : StandingAssumptions C lmo f L) : IsCompact C := h.1
theorem convex (h : StandingAssumptions C lmo f L) : Convex ℝ C := h.2.1
theorem isLMO (h : StandingAssumptions C lmo f L) : IsLMO C lmo := h.2.2.1
theorem convexOn (h : StandingAssumptions C lmo f L) : ConvexOn ℝ Set.univ f := h.2.2.2.1
theorem isSmooth (h : StandingAssumptions C lmo f L) : IsSmooth f L := h.2.2.2.2.1
theorem L_pos (h : StandingAssumptions C lmo f L) : 0 < L := h.2.2.2.2.2
theorem lmo_mem (h : StandingAssumptions C lmo f L) (g : StrongDual ℝ E) : lmo g ∈ C :=
  (h.isLMO g).1

end StandingAssumptions

/-- One Frank–Wolfe step from a feasible `x` with step size `γ ≥ 0`:
`f x⁺ - f x⋆ ≤ (1 - γ)(f x - f x⋆) + γ² L D² / 2`. -/
theorem step_bound {C : Set E} {lmo : StrongDual ℝ E → E} {f : E → ℝ} {L : NNReal}
    (h : StandingAssumptions C lmo f L) {x xStar : E} (hx : x ∈ C) (hxs : xStar ∈ minimizers C f)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    f (fwStep lmo (fderiv ℝ f) x γ) - f xStar ≤
      (1 - γ) * (f x - f xStar) + γ ^ 2 * L / 2 * Metric.diam C ^ 2 := by
  have hcpt := h.isCompact; have hlmo := h.isLMO; have hconv := h.convexOn
  have hsm := h.isSmooth
  set v := lmo (fderiv ℝ f x)
  have hprog := hsm.progress x v γ
  have hopt : fderiv ℝ f x v ≤ fderiv ℝ f x xStar := (hlmo (fderiv ℝ f x)).2 xStar hxs.1
  have hfo := add_fderiv_le_of_convexOn hconv hsm.1 x xStar
  have hgap : f x - f xStar ≤ fderiv ℝ f x (x - v) := by
    rw [map_sub] at hfo ⊢; linarith
  have hd : ‖v - x‖ ≤ Metric.diam C := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hcpt.isBounded (hlmo _).1 hx
  have hd2 : ‖v - x‖ ^ 2 ≤ Metric.diam C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hL : (0 : ℝ) ≤ γ ^ 2 * L / 2 := by positivity
  have : fwStep lmo (fderiv ℝ f) x γ = x + γ • (v - x) := rfl
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hgap hγ, mul_le_mul_of_nonneg_left hd2 hL]

/-- The short step does at least as well as any `γ ∈ [0, 1]` in the quadratic model. -/
theorem shortStep_le {C : Set E} {lmo : StrongDual ℝ E → E} {f : E → ℝ} {L : NNReal}
    (h : StandingAssumptions C lmo f L) {x : E} (hx : x ∈ C) {γ : ℝ}
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    f (fwStep lmo (fderiv ℝ f) x (shortStep lmo (fderiv ℝ f) L t x)) ≤
      f x - γ * fderiv ℝ f x (x - lmo (fderiv ℝ f x)) +
        γ ^ 2 * L / 2 * ‖lmo (fderiv ℝ f x) - x‖ ^ 2 := by
  have hlmo := h.isLMO; have hsm := h.isSmooth; have hL := h.L_pos
  set v := lmo (fderiv ℝ f x)
  set g := fderiv ℝ f x (x - v)
  set d := ‖v - x‖
  have hg : 0 ≤ g := by
    have := (hlmo (fderiv ℝ f x)).2 x hx
    simp only [g, map_sub]; linarith
  have hL' : (0 : ℝ) < L := hL
  set γs := min (g / (L * d ^ 2)) 1 with hγs
  have hstep : shortStep lmo (fderiv ℝ f) L t x = γs := rfl
  rw [hstep]
  refine (hsm.progress x v γs).trans ?_
  obtain ⟨hγ0, hγ1⟩ := hγ
  rcases eq_or_lt_of_le (norm_nonneg (v - x)) with hd0 | hd0
  · -- `v = x`: the gap vanishes and every step size gives the same value
    have hv : v = x := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hd0.symm
    have hg0 : g = 0 := by simp [g, hv]
    have hgoal : f x - γs * fderiv ℝ f x (x - v) + γs ^ 2 * L / 2 * ‖v - x‖ ^ 2 = f x := by
      rw [hv]; simp
    have hgoal' : f x - γ * fderiv ℝ f x (x - v) + γ ^ 2 * L / 2 * ‖v - x‖ ^ 2 = f x := by
      rw [hv]; simp
    rw [hgoal, hgoal']
  · have hLd : 0 < (L : ℝ) * d ^ 2 := by positivity
    -- `q(γ) - q(γs) = (γ - γs) (L d² (γ + γs) / 2 - g) ≥ 0`
    have key : -γs * g + γs ^ 2 * L / 2 * d ^ 2 ≤ -γ * g + γ ^ 2 * L / 2 * d ^ 2 := by
      rcases le_total (g / (L * d ^ 2)) 1 with hle | hle
      · have hγs' : γs = g / (L * d ^ 2) := min_eq_left hle
        have hgdef : g = γs * (L * d ^ 2) := by rw [hγs', div_mul_cancel₀ g (ne_of_gt hLd)]
        rw [hgdef]; nlinarith [sq_nonneg (γ - γs), hLd]
      · have hγs' : γs = 1 := min_eq_right hle
        have hg1 : L * d ^ 2 ≤ g := by rwa [le_div_iff₀ hLd, one_mul] at hle
        have h1 : 0 ≤ (1 - γ) * (g - L * d ^ 2 * (γ + 1) / 2) :=
          mul_nonneg (by linarith) (by nlinarith [hLd])
        rw [hγs']; nlinarith [h1]
    linarith

/-- The `1/t` recursion: if `h (t+1) ≤ (1 - 2/(t+2)) h t + (2/(t+2))² K/2` for all `t` and
`K ≥ 0`, then `h t ≤ 2K/(t+2)` for every `t ≥ 1`. -/
theorem rate_of_recursion {h : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hrec : ∀ t : ℕ, h (t + 1) ≤ (1 - 2 / ((t : ℝ) + 2)) * h t + (2 / ((t : ℝ) + 2)) ^ 2 * K / 2) :
    ∀ t : ℕ, 1 ≤ t → h t ≤ 2 * K / ((t : ℝ) + 2) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have := hrec 0
    norm_num at this ⊢
    linarith
  | succ t ht ih =>
    have h1 := hrec t
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    set s : ℝ := (t : ℝ) + 2 with hs
    have hspos : 0 < s := by positivity
    have hc : 0 ≤ 1 - 2 / s := by
      rw [sub_nonneg, div_le_one hspos]; linarith
    have h2 := mul_le_mul_of_nonneg_left ih hc
    have e : (1 - 2 / s) * (2 * K / s) + (2 / s) ^ 2 * K / 2 = 2 * K * (s - 1) / s ^ 2 := by
      field_simp; ring
    have hle : 2 * K * (s - 1) / s ^ 2 ≤ 2 * K / (s + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hK]
    have hcast : ((t + 1 : ℕ) : ℝ) + 2 = s + 1 := by push_cast; ring
    rw [hcast]; linarith

/-- The standard rate for a rule that does at least as well as `γ_t = 2/(t + 2)` at every step. -/
theorem rate_of_dominated {C : Set E} {lmo : StrongDual ℝ E → E} {f : E → ℝ} {L : NNReal}
    (h : StandingAssumptions C lmo f L) {step : ℕ → E → ℝ}
    (hstep : ∀ t, ∀ x ∈ C, step t x ∈ Set.Icc (0 : ℝ) 1)
    (hdom : ∀ t, ∀ x ∈ C, f (fwStep lmo (fderiv ℝ f) x (step t x)) ≤
      f (x + (2 / ((t : ℝ) + 2)) • (lmo (fderiv ℝ f x) - x)) ∨
      f (fwStep lmo (fderiv ℝ f) x (step t x)) ≤
        f x - 2 / ((t : ℝ) + 2) * fderiv ℝ f x (x - lmo (fderiv ℝ f x)) +
          (2 / ((t : ℝ) + 2)) ^ 2 * L / 2 * ‖lmo (fderiv ℝ f x) - x‖ ^ 2)
    {xStar : E} (hxs : xStar ∈ minimizers C f) {x₀ : E} (hx₀ : x₀ ∈ C) :
    ∀ t : ℕ, 1 ≤ t → f (fwIterates lmo (fderiv ℝ f) step x₀ t) - f xStar ≤
      2 * L * Metric.diam C ^ 2 / ((t : ℝ) + 2) := by
  have hmem := fwIterates_mem h.convex h.lmo_mem (fderiv ℝ f) hstep hx₀
  have hK : (0 : ℝ) ≤ L * Metric.diam C ^ 2 := by positivity
  have key := rate_of_recursion (h := fun t => f (fwIterates lmo (fderiv ℝ f) step x₀ t) - f xStar)
    hK fun t => by
      set x := fwIterates lmo (fderiv ℝ f) step x₀ t
      have hx : x ∈ C := hmem t
      have hγ0 : (0 : ℝ) ≤ 2 / ((t : ℝ) + 2) := by positivity
      have hb := step_bound h hx hxs hγ0
      have hsucc : fwIterates lmo (fderiv ℝ f) step x₀ (t + 1) = fwStep lmo (fderiv ℝ f) x (step t x) := rfl
      simp only [hsucc]
      rcases hdom t x hx with hd | hd
      · have : fwStep lmo (fderiv ℝ f) x (2 / ((t : ℝ) + 2)) =
            x + (2 / ((t : ℝ) + 2)) • (lmo (fderiv ℝ f x) - x) := rfl
        rw [this] at hb
        nlinarith
      · -- the model bound at `γ = 2/(t+2)` is the bound of `step_bound`'s proof
        have hcpt := h.isCompact; have hlmo := h.isLMO; have hconv := h.convexOn
        have hsm := h.isSmooth
        have hopt := (hlmo (fderiv ℝ f x)).2 xStar hxs.1
        have hfo := add_fderiv_le_of_convexOn hconv hsm.1 x xStar
        have hgap : f x - f xStar ≤ fderiv ℝ f x (x - lmo (fderiv ℝ f x)) := by
          rw [map_sub] at hfo ⊢; linarith
        have hd' : ‖lmo (fderiv ℝ f x) - x‖ ≤ Metric.diam C := by
          rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hcpt.isBounded (hlmo _).1 hx
        have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd' 2
        have hL : (0 : ℝ) ≤ (2 / ((t : ℝ) + 2)) ^ 2 * L / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hgap hγ0, mul_le_mul_of_nonneg_left hd2 hL]
  intro t ht
  have := key t ht
  simpa [mul_assoc] using this

end Lemmata.FrankWolfe
