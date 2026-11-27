module

public import Lemmata.CGBasics.FixedStep
public import Lemmata.CGBasics.Rates

@[expose] public section

/-!
# Uniformly convex sets (Proposition 2.19, Theorems 2.20 and 2.24)

Near the minimizer `v` of `ψ`, a uniformly convex set curves away from the supporting hyperplane:
moving from `x` toward `v` and then by `θ (1 - θ) α ‖x - v‖^q` in any unit direction stays inside.
This gives the scaling inequality `α ‖ψ‖ ‖x - v‖^q ≤ ψ(x - v)`, which turns the progress of a
short step into a contraction of the primal gap.
-/

namespace Lemmata.CGBasics

open Lemmata.FrankWolfe

universe u

namespace Proof

theorem uniformly_convex_scaling : UniformlyConvexScaling.{u} := by
  intro E _ _ C α q hUC ψ v hv hmin x hx
  set A := α * ‖x - v‖ ^ q with hA
  have hgap : 0 ≤ ψ (x - v) := by rw [map_sub]; linarith [hmin x hx]
  have hre : α * ‖ψ‖ * ‖x - v‖ ^ q = A * ‖ψ‖ := by rw [hA]; ring
  rcases le_or_gt A 0 with hA0 | hApos
  · rw [hre]; nlinarith [norm_nonneg ψ]
  have hkey : ∀ z : E, ‖z‖ = 1 → A * (-ψ z) ≤ ψ (x - v) := by
    intro z hz
    by_contra hlt
    push Not at hlt
    set K := A * (-ψ z) with hK
    have hKpos : 0 < K := lt_of_le_of_lt hgap hlt
    set θ := (ψ (x - v) / K + 1) / 2 with hθ
    have hr0 : 0 ≤ ψ (x - v) / K := div_nonneg hgap hKpos.le
    have hr1 : ψ (x - v) / K < 1 := (div_lt_one hKpos).mpr hlt
    have hθ0 : 0 < θ := by rw [hθ]; linarith
    have hθ1 : θ < 1 := by rw [hθ]; linarith
    have hθK : θ * K = (ψ (x - v) + K) / 2 := by
      rw [hθ]; field_simp
    have hm := hUC v hv x hx θ ⟨hθ0.le, hθ1.le⟩ z hz
    have hle := hmin _ hm
    rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      norm_sub_rev] at hle
    have e : θ * ψ v + (1 - θ) * ψ x + θ * (1 - θ) * α * ‖x - v‖ ^ q * ψ z - ψ v =
        (1 - θ) * (ψ x - ψ v - θ * K) := by
      rw [hK, hA]; ring
    have h1 : 0 < 1 - θ := by linarith
    have h2 : 0 ≤ ψ x - ψ v - θ * K := (mul_nonneg_iff_of_pos_left h1).mp (by linarith)
    rw [map_sub] at hlt hgap hθK
    linarith
  have hbound : ‖ψ‖ ≤ ψ (x - v) / A := by
    refine ContinuousLinearMap.opNorm_le_bound ψ (div_nonneg hgap hApos.le) (fun z => ?_)
    rcases eq_or_ne z 0 with hz | hz
    · simp [hz]
    · set u := (‖z‖⁻¹ : ℝ) • z with hu
      have hun : ‖u‖ = 1 := norm_smul_inv_norm hz
      have h1 := hkey u hun
      have h2 := hkey (-u) (by rw [norm_neg, hun])
      rw [map_neg, neg_neg] at h2
      have hψu : |ψ u| ≤ ψ (x - v) / A := by
        rw [abs_le]
        constructor
        · rw [neg_le, le_div_iff₀ hApos]; linarith
        · rw [le_div_iff₀ hApos]; linarith
      have hz' : ψ z = ‖z‖ * ψ u := by
        rw [hu, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),
          one_mul]
      rw [Real.norm_eq_abs, hz', abs_mul, abs_norm, mul_comm]
      exact mul_le_mul_of_nonneg_right hψu (norm_nonneg z)
  calc α * ‖ψ‖ * ‖x - v‖ ^ q = A * ‖ψ‖ := hre
    _ ≤ A * (ψ (x - v) / A) := mul_le_mul_of_nonneg_left hbound hApos.le
    _ = ψ (x - v) := mul_div_cancel₀ _ hApos.ne'

/-- Progress of a short step under the scaling inequality `β ‖d‖^q ≤ g` with `h ≤ g`. -/
theorem uc_progress {L g n h β q Δ : ℝ} (hL : 0 < L) (hq : 2 ≤ q) (hβ : 0 < β) (hhg : h ≤ g)
    (h0 : 0 ≤ h) (hn : 0 ≤ n) (hscal : β * n ^ q ≤ g)
    (hstep : ∀ s ∈ Set.Icc (0 : ℝ) 1, s * g - s ^ 2 * L / 2 * n ^ 2 ≤ Δ) :
    h * min (1 / 2) (β ^ (2 / q) * h ^ (1 - 2 / q) / (2 * L)) ≤ Δ := by
  have hΔ0 : 0 ≤ Δ := by simpa using hstep 0 ⟨le_rfl, zero_le_one⟩
  have hminle : h * min (1 / 2) (β ^ (2 / q) * h ^ (1 - 2 / q) / (2 * L)) ≤ h * (1 / 2) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) h0
  rcases eq_or_lt_of_le h0 with hz | hhpos
  · rw [← hz, zero_mul]; exact hΔ0
  have hgpos : 0 < g := lt_of_lt_of_le hhpos hhg
  by_cases hbig : L * n ^ 2 ≤ g
  · have h1 := hstep 1 ⟨zero_le_one, le_rfl⟩
    nlinarith
  push Not at hbig
  have hLn : 0 < L * n ^ 2 := lt_trans hgpos hbig
  set s := g / (L * n ^ 2) with hs
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hgpos.le hLn.le, (div_le_one hLn).mpr hbig.le⟩
  have h1 := hstep s hs01
  have hval : s * g - s ^ 2 * L / 2 * n ^ 2 = g ^ 2 / (2 * (L * n ^ 2)) := by
    rw [hs]; field_simp; ring
  have hq0 : 0 < q := by linarith
  have hnq : n ^ q ≤ g / β := by rw [le_div_iff₀ hβ]; linarith
  have hn2 : n ^ 2 ≤ (g / β) ^ (2 / q) := by
    calc n ^ 2 = n ^ (2 : ℝ) := (Real.rpow_two n).symm
      _ = (n ^ q) ^ (2 / q) := by rw [← Real.rpow_mul hn]; congr 1; field_simp
      _ ≤ (g / β) ^ (2 / q) := Real.rpow_le_rpow (Real.rpow_nonneg hn q) hnq (by positivity)
  have hgb : g ^ 2 / (2 * (L * (g / β) ^ (2 / q))) = β ^ (2 / q) * g ^ (2 - 2 / q) / (2 * L) := by
    rw [Real.div_rpow hgpos.le hβ.le, Real.rpow_sub hgpos, Real.rpow_two]
    have : 0 < g ^ (2 / q) := Real.rpow_pos_of_pos hgpos _
    have : 0 < β ^ (2 / q) := Real.rpow_pos_of_pos hβ _
    field_simp
  have hcmp : g ^ 2 / (2 * (L * (g / β) ^ (2 / q))) ≤ g ^ 2 / (2 * (L * n ^ 2)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg g) (by positivity)
    nlinarith
  have hexp : 0 ≤ 2 - 2 / q := by
    have : 2 / q ≤ 1 := by rw [div_le_one hq0]; linarith
    linarith
  have hmono : h ^ (2 - 2 / q) ≤ g ^ (2 - 2 / q) := Real.rpow_le_rpow h0 hhg hexp
  have hsplit : h ^ (2 - 2 / q) = h * h ^ (1 - 2 / q) := by
    rw [show (2 : ℝ) - 2 / q = 1 + (1 - 2 / q) by ring, Real.rpow_add hhpos, Real.rpow_one]
  have hβq : 0 < β ^ (2 / q) := Real.rpow_pos_of_pos hβ _
  have hfin : h * (β ^ (2 / q) * h ^ (1 - 2 / q) / (2 * L)) ≤
      β ^ (2 / q) * g ^ (2 - 2 / q) / (2 * L) := by
    rw [show h * (β ^ (2 / q) * h ^ (1 - 2 / q) / (2 * L)) =
      β ^ (2 / q) * (h * h ^ (1 - 2 / q)) / (2 * L) by ring, ← hsplit]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmono hβq.le
  have hminle2 := mul_le_mul_of_nonneg_left
    (min_le_right (1 / 2) (β ^ (2 / q) * h ^ (1 - 2 / q) / (2 * L))) h0
  linarith

/-- The facts used for every step of a short-step run. -/
theorem run_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {f : E → ℝ}
    {L : NNReal} {x v : ℕ → E} {γ : ℕ → ℝ} (hCc : Convex ℝ C) (hconv : ConvexOn ℝ Set.univ f)
    (hsm : IsSmooth f L) (hrun : IsShortStepRun C f L x v γ) {xStar : E}
    (hxs : xStar ∈ minimizers C f) (t : ℕ) :
    x t ∈ C ∧ f (x t) - f xStar ≤ fderiv ℝ f (x t) (x t - v t) ∧ f xStar ≤ f (x (t + 1)) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, s * fderiv ℝ f (x t) (x t - v t) - s ^ 2 * L / 2 *
        ‖v t - x t‖ ^ 2 ≤ f (x t) - f (x (t + 1)) := by
  have hxC := iterates_mem hCc hrun.1 (fun t => ⟨(hrun.2 t).1, (hrun.2 t).2.2.1,
    (hrun.2 t).2.2.2.1⟩)
  refine ⟨hxC t, ?_, hxs.2 _ (hxC (t + 1)), fun s hs => by linarith [(hrun.2 t).2.2.2.2 s hs]⟩
  have h1 := add_fderiv_le_of_convexOn hconv hsm.1 (x t) xStar
  have h2 := (hrun.2 t).2.1 xStar hxs.1
  rw [map_sub] at h1 ⊢
  linarith

theorem uniformly_convex_linear : UniformlyConvexLinear.{u} := by
  intro E _ _ C f L α c x v γ hC hCc hUC hα hc hL hconv hsm hgrad hrun xStar hxs t ht
  set D := Metric.diam C with hD
  set c₁ := min (1 / 2 : ℝ) (α * c / (2 * L)) with hc₁
  have hc₁pos : 0 < c₁ := lt_min (by norm_num) (by positivity)
  have hc₁lt : c₁ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hfirst : f (x 1) - f xStar ≤ L * D ^ 2 / 2 := by
    have := (vanilla_rate C f L x v γ hC hCc hconv hsm hrun.1 hrun.2 xStar hxs 1 le_rfl).1
    have e : 2 * (L : ℝ) * D ^ 2 / (((1 : ℕ) : ℝ) + 3) = L * D ^ 2 / 2 := by push_cast; ring
    linarith
  have hstep : ∀ τ, 1 ≤ τ → (f (x τ) - f xStar) * c₁ ≤
      (f (x τ) - f xStar) - (f (x (τ + 1)) - f xStar) := by
    intro τ _
    obtain ⟨hxτ, hhg, hlow, hs⟩ := run_step hCc hconv hsm hrun hxs τ
    have hh0 : 0 ≤ f (x τ) - f xStar := by linarith [hxs.2 _ hxτ]
    have hscal : α * c * ‖v τ - x τ‖ ^ (2 : ℝ) ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      have h1 := uniformly_convex_scaling C α 2 hUC (fderiv ℝ f (x τ)) (v τ) ((hrun.2 τ).1)
        ((hrun.2 τ).2.1) (x τ) hxτ
      rw [norm_sub_rev]
      have := hgrad _ hxτ
      nlinarith [Real.rpow_nonneg (norm_nonneg (x τ - v τ)) 2]
    have := uc_progress (L := L) (q := 2) hL le_rfl (by positivity) hhg hh0 (norm_nonneg _)
      hscal hs
    have e : (α * c) ^ (2 / (2 : ℝ)) * (f (x τ) - f xStar) ^ (1 - 2 / (2 : ℝ)) / (2 * L) =
        α * c / (2 * L) := by
      norm_num
    rw [e] at this
    linarith
  have := contraction_linear (fun τ => f (x τ) - f xStar) (L * D ^ 2 / 2) c₁
    (fun τ => by have := (run_step hCc hconv hsm hrun hxs τ).1; linarith [hxs.2 _ this])
    hc₁pos hc₁lt hfirst hstep t ht
  have e : 1 - c₁ = max (1 / 2) (1 - α * c / (2 * L)) := by
    rw [hc₁]
    rcases le_total (1 / 2 : ℝ) (α * c / (2 * L)) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; norm_num
    · rw [min_eq_right h, max_eq_right (by linarith)]
  rw [e, mul_comm] at this
  exact this

/-- `contraction_mixed` with `c₁ = 1/2` for a nonnegative, nonincreasing sequence that contracts
while it is positive, evaluated at a single time `T ≥ 1`. -/
theorem rate_assembly (h : ℕ → ℝ) (c₀ c₂ a : ℝ) (hc₀ : 0 < c₀) (hc₂ : 0 < c₂) (ha : 0 < a)
    (h0 : ∀ t, 0 ≤ h t) (hmono : ∀ t, h (t + 1) ≤ h t) (h1 : h 1 ≤ c₀)
    (hstep : ∀ t, 1 ≤ t → 0 < h t → h t * min (1 / 2) (c₂ * h t ^ a) ≤ h t - h (t + 1))
    (T : ℕ) (hT : 1 ≤ T) :
    ((T : ℤ) < max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / c₀)⌋ + 2) 1 →
        h T ≤ c₀ * (1 - 1 / 2) ^ (T - 1)) ∧
      (max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / c₀)⌋ + 2) 1 ≤ (T : ℤ) →
        h T ≤ (1 / 2 / c₂) ^ (1 / a) / (1 + 1 / 2 * a * ((T : ℝ) -
          (max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / c₀)⌋ + 2) 1 : ℤ))) ^ (1 / a)) := by
  set t₀ : ℤ := max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / c₀)⌋ + 2) 1 with ht₀
  rcases eq_or_lt_of_le (h0 T) with hz | hTpos
  · refine ⟨fun _ => by rw [← hz]; positivity, fun hge => ?_⟩
    rw [← hz]
    have : (0 : ℝ) ≤ (T : ℝ) - (t₀ : ℝ) := by
      have : (t₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hge
      linarith
    positivity
  have hanti : Antitone h := antitone_nat_of_succ_le hmono
  have hpos : ∀ t ≤ T, 0 < h t := fun t ht => lt_of_lt_of_le hTpos (hanti ht)
  set φ : ℝ → ℝ := fun y => y - y * min (1 / 2) (c₂ * y ^ a) with hφ
  have hφpos : ∀ y, 0 < y → 0 < φ y := fun y hy => by
    have : min (1 / 2 : ℝ) (c₂ * y ^ a) ≤ 1 / 2 := min_le_left _ _
    simp only [hφ]; nlinarith
  have hiter : ∀ k, 0 < φ^[k] (h T) := by
    intro k
    induction k with
    | zero => exact hTpos
    | succ k ih => rw [Function.iterate_succ_apply']; exact hφpos _ ih
  set h' : ℕ → ℝ := fun n => if n ≤ T then h n else φ^[n - T] (h T) with hh'
  have hh'pos : ∀ n, 0 < h' n := by
    intro n
    simp only [hh']
    split_ifs with hn
    · exact hpos n hn
    · exact hiter _
  have hstep' : ∀ t, 1 ≤ t → h' t * min (1 / 2) (c₂ * h' t ^ a) ≤ h' t - h' (t + 1) := by
    intro t ht
    by_cases htT : t < T
    · have e1 : h' t = h t := by simp [hh', htT.le]
      have e2 : h' (t + 1) = h (t + 1) := by simp [hh', Nat.succ_le_of_lt htT]
      rw [e1, e2]; exact hstep t ht (hpos t htT.le)
    · push Not at htT
      have e2 : h' (t + 1) = φ (h' t) := by
        have hn1 : ¬ (t + 1 ≤ T) := by omega
        rcases eq_or_lt_of_le htT with heq | hlt
        · subst heq
          simp [hh', hn1]
        · have hn2 : ¬ (t ≤ T) := by omega
          simp only [hh', hn1, hn2, ite_false]
          rw [show t + 1 - T = (t - T) + 1 by omega, Function.iterate_succ_apply']
      rw [e2, hφ]
      simp only
      linarith
  have h1' : h' 1 ≤ c₀ := by simp [hh', hT]; exact h1
  have hm := contraction_mixed h' c₀ (1 / 2) c₂ a hh'pos hc₀ (by norm_num) (by norm_num) hc₂ ha h1'
    hstep'
  have hT' : h' T = h T := by simp [hh']
  rw [← hT']
  exact ⟨fun hlt => hm.1 T hT hlt, fun hge => hm.2 T hge⟩

theorem t0_eq (L D K : ℝ) (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    max (⌊Real.logb (1 - 1 / 2) (L * K / (L * D ^ 2 / 2))⌋ + 2) 1 =
      max (⌊Real.logb 2 (D ^ 2 / K)⌋ + 1) (1 : ℤ) := by
  have e : Real.logb (1 - 1 / 2) (L * K / (L * D ^ 2 / 2)) = Real.logb 2 (D ^ 2 / K) - 1 := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num,
      show L * K / (L * D ^ 2 / 2) = 2 * K / D ^ 2 by field_simp]
    simp only [Real.logb, Real.log_inv]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hK.ne',
      Real.log_div (by positivity) hK.ne']
    field_simp
    ring
  rw [e, Int.floor_sub_one]
  congr 1
  ring

theorem first_regime (L D : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    L * D ^ 2 / 2 * (1 - 1 / 2) ^ (t - 1) = L * D ^ 2 / 2 ^ t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow, pow_succ]
  field_simp
  ring

theorem uniformly_convex_power : UniformlyConvexPower.{u} := by
  intro E _ _ C f L α c q x v γ hC hCc hUC hq hα hc hL hconv hsm hgrad hrun xStar hxs K t₀
  set D := Metric.diam C with hD
  have hq0 : 0 < q := by linarith
  have hKdef : K = ((L : ℝ) / (α * c)) ^ (2 / (q - 2)) := rfl
  have hK : 0 < K := by rw [hKdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have ht0def : t₀ = max (⌊Real.logb 2 (D ^ 2 / K)⌋ + 1) 1 := rfl
  set h : ℕ → ℝ := fun τ => f (x τ) - f xStar with hh
  have hfacts := run_step hCc hconv hsm hrun hxs
  have h0 : ∀ τ, 0 ≤ h τ := fun τ => by simp only [hh]; linarith [hxs.2 _ (hfacts τ).1]
  have hmono : ∀ τ, h (τ + 1) ≤ h τ := fun τ => by
    have := (hfacts τ).2.2.2 0 ⟨le_rfl, zero_le_one⟩
    simp only [hh]; simp at this; linarith
  have hvan : ∀ τ : ℕ, 1 ≤ τ → h τ ≤ 2 * L * D ^ 2 / ((τ : ℝ) + 3) := fun τ hτ =>
    (vanilla_rate C f L x v γ hC hCc hconv hsm hrun.1 hrun.2 xStar hxs τ hτ).1
  have h1 : h 1 ≤ L * D ^ 2 / 2 := by
    have := hvan 1 le_rfl
    have e : 2 * (L : ℝ) * D ^ 2 / (((1 : ℕ) : ℝ) + 3) = L * D ^ 2 / 2 := by push_cast; ring
    linarith
  have hbase : ∀ t : ℕ, t₀ ≤ (t : ℤ) → 0 ≤ (t : ℝ) - (t₀ : ℝ) := fun t ht => by
    have : (t₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hq2 : 0 ≤ 1 / 2 - 1 / q := by
    have : 1 / q ≤ 1 / 2 := by rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
    linarith
  rcases eq_or_lt_of_le (Metric.diam_nonneg : 0 ≤ D) with hD0 | hDpos
  · have hD0' : D = 0 := hD0.symm
    have hz : ∀ τ : ℕ, 1 ≤ τ → h τ ≤ 0 := fun τ hτ => by
      have := hvan τ hτ
      rw [hD0'] at this
      simpa using this
    refine ⟨fun t ht _ => ?_, fun t ht => ?_⟩
    · have := hz t ht
      simp only [hh] at this
      rw [hD0']
      simp
      linarith
    have ht1 : 1 ≤ t := by
      have : (1 : ℤ) ≤ t₀ := le_max_right _ _
      omega
    have h2 := hz t ht1
    have h3 := hbase t ht
    have : 0 ≤ L * K / (1 + (1 / 2 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 2)) := by positivity
    simp only [hh] at h2
    linarith
  set c₂ := (α * c) ^ (2 / q) / (2 * L) with hc₂
  set a := 1 - 2 / q with ha
  have hapos : 0 < a := by
    rw [ha]
    have : 2 / q < 1 := by rw [div_lt_one hq0]; exact hq
    linarith
  have hc₂pos : 0 < c₂ := by positivity
  have hstep : ∀ τ, 1 ≤ τ → 0 < h τ → h τ * min (1 / 2) (c₂ * h τ ^ a) ≤ h τ - h (τ + 1) := by
    intro τ _ _
    obtain ⟨hxτ, hhg, _, hs⟩ := hfacts τ
    have hscal : α * c * ‖v τ - x τ‖ ^ q ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      have h1 := uniformly_convex_scaling C α q hUC (fderiv ℝ f (x τ)) (v τ) ((hrun.2 τ).1)
        ((hrun.2 τ).2.1) (x τ) hxτ
      rw [norm_sub_rev]
      have := hgrad _ hxτ
      nlinarith [Real.rpow_nonneg (norm_nonneg (x τ - v τ)) q]
    have := uc_progress hL hq.le (by positivity) hhg (h0 τ) (norm_nonneg _) hscal hs
    have e : (α * c) ^ (2 / q) * h τ ^ (1 - 2 / q) / (2 * L) = c₂ * h τ ^ a := by
      rw [hc₂, ha]; ring
    simp only [hh] at e ⊢
    rw [e] at this
    linarith
  have hτ : (1 / 2 / c₂) ^ (1 / a) = L * K := by
    have hac : 0 < α * c := by positivity
    have e1 : 1 / 2 / c₂ = L / (α * c) ^ (2 / q) := by
      rw [hc₂]; field_simp
    have e2 : 1 / a = q / (q - 2) := by
      rw [ha]; field_simp
    rw [e1, e2, Real.div_rpow hL.le (Real.rpow_nonneg hac.le _), ← Real.rpow_mul hac.le, hKdef,
      Real.div_rpow hL.le hac.le,
      show 2 / q * (q / (q - 2)) = 2 / (q - 2) by field_simp,
      show q / (q - 2) = 1 + 2 / (q - 2) by field_simp; ring, Real.rpow_add hL, Real.rpow_one]
    ring
  have ht0 : max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / (L * D ^ 2 / 2))⌋ + 2) 1 =
      t₀ := by
    rw [hτ, ht0def]; exact t0_eq L D K hL hDpos hK
  refine ⟨fun t ht hlt => ?_, fun t hge => ?_⟩
  · have := (rate_assembly h (L * D ^ 2 / 2) c₂ a (by positivity) hc₂pos hapos h0 hmono h1 hstep
      t ht).1 (by rw [ht0]; exact hlt)
    rw [first_regime L D t ht] at this
    exact this
  · have ht1 : 1 ≤ t := by
      have : (1 : ℤ) ≤ t₀ := le_max_right _ _
      omega
    have := (rate_assembly h (L * D ^ 2 / 2) c₂ a (by positivity) hc₂pos hapos h0 hmono h1 hstep
      t ht1).2 (by rw [ht0]; exact hge)
    rw [ht0, hτ] at this
    have e1 : (1 / 2 : ℝ) * a = 1 / 2 - 1 / q := by rw [ha]; ring
    have e2 : 1 / a = q / (q - 2) := by rw [ha]; field_simp
    rw [e1, e2] at this
    exact this

theorem gradient_dominated_rate : GradientDominatedRate.{u} := by
  intro E _ _ C f L α c q x v γ hC hCc hUC hq hα hc hL hconv hsm hgd hrun xStar hxs K t₀
  set D := Metric.diam C with hD
  have hq0 : 0 < q := by linarith
  have hKdef : K = ((L : ℝ) * c ^ 2 / α ^ 2) ^ (1 / (q - 1)) := rfl
  have hK : 0 < K := by rw [hKdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have ht0def : t₀ = max (⌊Real.logb 2 (D ^ 2 / K)⌋ + 1) 1 := rfl
  set h : ℕ → ℝ := fun τ => f (x τ) - f xStar with hh
  have hfacts := run_step hCc hconv hsm hrun hxs
  have h0 : ∀ τ, 0 ≤ h τ := fun τ => by simp only [hh]; linarith [hxs.2 _ (hfacts τ).1]
  have hmono : ∀ τ, h (τ + 1) ≤ h τ := fun τ => by
    have := (hfacts τ).2.2.2 0 ⟨le_rfl, zero_le_one⟩
    simp only [hh]; simp at this; linarith
  have hvan : ∀ τ : ℕ, 1 ≤ τ → h τ ≤ 2 * L * D ^ 2 / ((τ : ℝ) + 3) := fun τ hτ =>
    (vanilla_rate C f L x v γ hC hCc hconv hsm hrun.1 hrun.2 xStar hxs τ hτ).1
  have h1 : h 1 ≤ L * D ^ 2 / 2 := by
    have := hvan 1 le_rfl
    have e : 2 * (L : ℝ) * D ^ 2 / (((1 : ℕ) : ℝ) + 3) = L * D ^ 2 / 2 := by push_cast; ring
    linarith
  have hbase : ∀ t : ℕ, t₀ ≤ (t : ℤ) → 0 ≤ (t : ℝ) - (t₀ : ℝ) := fun t ht => by
    have : (t₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hq2 : 0 ≤ 1 / 2 * (1 - 1 / q) := by
    have : 1 / q ≤ 1 := by rw [div_le_one hq0]; linarith
    linarith
  rcases eq_or_lt_of_le (Metric.diam_nonneg : 0 ≤ D) with hD0 | hDpos
  · have hD0' : D = 0 := hD0.symm
    have hz : ∀ τ : ℕ, 1 ≤ τ → h τ ≤ 0 := fun τ hτ => by
      have := hvan τ hτ
      rw [hD0'] at this
      simpa using this
    refine ⟨fun t ht _ => ?_, fun t ht => ?_⟩
    · have := hz t ht
      simp only [hh] at this
      rw [hD0']
      simp
      linarith
    have ht1 : 1 ≤ t := by
      have : (1 : ℤ) ≤ t₀ := le_max_right _ _
      omega
    have h2 := hz t ht1
    have h3 := hbase t ht
    have : 0 ≤ L * K / (1 + 1 / 2 * (1 - 1 / q) * ((t : ℝ) - t₀)) ^ (q / (q - 1)) := by positivity
    simp only [hh] at h2
    linarith
  set c₂ := (α / c) ^ (2 / q) / (2 * L) with hc₂
  set a := 1 - 1 / q with ha
  have hapos : 0 < a := by
    rw [ha]
    have : 1 / q < 1 := by rw [div_lt_one hq0]; linarith
    linarith
  have hc₂pos : 0 < c₂ := by positivity
  have hstep : ∀ τ, 1 ≤ τ → 0 < h τ → h τ * min (1 / 2) (c₂ * h τ ^ a) ≤ h τ - h (τ + 1) := by
    intro τ _ hhpos
    obtain ⟨hxτ, hhg, _, hs⟩ := hfacts τ
    set β := α * Real.sqrt (h τ) / c with hβ
    have hβpos : 0 < β := by rw [hβ]; have := Real.sqrt_pos.mpr hhpos; positivity
    have hgrad : Real.sqrt (h τ) / c ≤ ‖fderiv ℝ f (x τ)‖ := by
      have h1 := hgd (x τ) hxτ xStar hxs.1
      rw [div_le_iff₀ hc]
      have h2 : h τ ≤ (c * ‖fderiv ℝ f (x τ)‖) ^ 2 := by
        rw [mul_pow]; simp only [hh]; rw [div_le_iff₀ (by positivity)] at h1; linarith
      calc Real.sqrt (h τ) ≤ Real.sqrt ((c * ‖fderiv ℝ f (x τ)‖) ^ 2) := Real.sqrt_le_sqrt h2
        _ = c * ‖fderiv ℝ f (x τ)‖ := Real.sqrt_sq (by positivity)
        _ = ‖fderiv ℝ f (x τ)‖ * c := mul_comm _ _
    have hscal : β * ‖v τ - x τ‖ ^ q ≤ fderiv ℝ f (x τ) (x τ - v τ) := by
      have h1 := uniformly_convex_scaling C α q hUC (fderiv ℝ f (x τ)) (v τ) ((hrun.2 τ).1)
        ((hrun.2 τ).2.1) (x τ) hxτ
      rw [norm_sub_rev]
      have h3 : β = α * (Real.sqrt (h τ) / c) := by rw [hβ]; ring
      rw [h3]
      have h4 : 0 ≤ ‖x τ - v τ‖ ^ q := Real.rpow_nonneg (norm_nonneg _) q
      have h5 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrad hα.le) h4
      linarith
    have := uc_progress hL hq (by positivity) hhg (h0 τ) (norm_nonneg _) hscal hs
    have e : β ^ (2 / q) * h τ ^ (1 - 2 / q) / (2 * L) = c₂ * h τ ^ a := by
      have hsq : Real.sqrt (h τ) ^ (2 / q) = h τ ^ (1 / q) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (h0 τ)]; congr 1; ring
      rw [hβ, show α * Real.sqrt (h τ) / c = α / c * Real.sqrt (h τ) by ring,
        Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), hsq, hc₂, ha, mul_assoc,
        ← Real.rpow_add hhpos]
      rw [show 1 / q + (1 - 2 / q) = 1 - 1 / q by ring]
      ring
    simp only [hh] at e ⊢
    rw [e] at this
    linarith
  have hτ : (1 / 2 / c₂) ^ (1 / a) = L * K := by
    have hq1 : 0 < q - 1 := by linarith
    have hac : 0 < α / c := by positivity
    have e1 : 1 / 2 / c₂ = L / (α / c) ^ (2 / q) := by
      rw [hc₂]; field_simp
    have e2 : 1 / a = q / (q - 1) := by
      rw [ha]; field_simp
    have lhs : (L / (α / c) ^ (2 / q)) ^ (q / (q - 1)) =
        (L : ℝ) ^ (q / (q - 1)) * c ^ (2 / (q - 1)) / α ^ (2 / (q - 1)) := by
      rw [Real.div_rpow hL.le (Real.rpow_nonneg hac.le _), ← Real.rpow_mul hac.le,
        show 2 / q * (q / (q - 1)) = 2 / (q - 1) by field_simp,
        Real.div_rpow hα.le hc.le]
      field_simp
    have rhs : (L : ℝ) * K = (L : ℝ) ^ (q / (q - 1)) * c ^ (2 / (q - 1)) / α ^ (2 / (q - 1)) := by
      have ec : (c ^ 2) ^ (1 / (q - 1)) = c ^ (2 / (q - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; congr 1; push_cast; ring
      have ea : (α ^ 2) ^ (1 / (q - 1)) = α ^ (2 / (q - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]; congr 1; push_cast; ring
      rw [hKdef, Real.div_rpow (by positivity) (by positivity),
        Real.mul_rpow (NNReal.coe_nonneg L) (by positivity), ec, ea,
        show q / (q - 1) = 1 + 1 / (q - 1) by field_simp; ring, Real.rpow_add hL, Real.rpow_one]
      ring
    rw [e1, e2, lhs, rhs]
  have ht0 : max (⌊Real.logb (1 - 1 / 2) ((1 / 2 / c₂) ^ (1 / a) / (L * D ^ 2 / 2))⌋ + 2) 1 =
      t₀ := by
    rw [hτ, ht0def]; exact t0_eq L D K hL hDpos hK
  refine ⟨fun t ht hlt => ?_, fun t hge => ?_⟩
  · have := (rate_assembly h (L * D ^ 2 / 2) c₂ a (by positivity) hc₂pos hapos h0 hmono h1 hstep
      t ht).1 (by rw [ht0]; exact hlt)
    rw [first_regime L D t ht] at this
    exact this
  · have ht1 : 1 ≤ t := by
      have : (1 : ℤ) ≤ t₀ := le_max_right _ _
      omega
    have := (rate_assembly h (L * D ^ 2 / 2) c₂ a (by positivity) hc₂pos hapos h0 hmono h1 hstep
      t ht1).2 (by rw [ht0]; exact hge)
    rw [ht0, hτ] at this
    have e1 : (1 / 2 : ℝ) * a = 1 / 2 * (1 - 1 / q) := by rw [ha]
    have e2 : 1 / a = q / (q - 1) := by rw [ha]; field_simp
    rw [e1, e2] at this
    exact this

end Proof

end Lemmata.CGBasics
