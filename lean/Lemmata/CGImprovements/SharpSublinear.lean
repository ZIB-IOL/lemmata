module

public import Lemmata.CGImprovements.SharpAFW
public import Lemmata.CGBasics.UniformlyConvex

@[expose] public section

/-!
# Sublinear rates under sharpness (Corollary 3.33 for `θ < 1/2`) and Lemma 3.35

A step of away-step Frank–Wolfe that does not drop a vertex maps the primal gap `h` below
`φ(h) = h - h min {1/2, c₂ h^{1-2θ}}` with `c₂ = δ²/(8 c² L D²)`. The map `φ` is monotone, so
after `G` such steps the gap is below the `G`-th iterate of `φ` from `L D²/2`, to which Lemma 2.21
applies; at least `⌊(t-1)/2⌋` of the first `t - 1` steps after the first one are such steps.
-/

namespace Lemmata.CGImprovements

open Lemmata.FrankWolfe

universe u

namespace Proof

/-- The contraction map `φ(z) = z - z min {1/2, c₂ z^a}` is monotone on `[0, ∞)` for
`0 < a ≤ 1`. -/
theorem contraction_mono {c₂ a : ℝ} (hc₂ : 0 < c₂) (ha : 0 < a) (ha1 : a ≤ 1) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    x - x * min (1 / 2) (c₂ * x ^ a) ≤ y - y * min (1 / 2) (c₂ * y ^ a) := by
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → c₂ * y ^ a ≤ 1 / 2 →
      x - x * (c₂ * x ^ a) ≤ y - y * (c₂ * y ^ a) := by
    intro x y hx hxy hy
    have hy0 : 0 ≤ y := hx.trans hxy
    have hya : 0 ≤ y ^ a := Real.rpow_nonneg hy0 a
    rcases eq_or_lt_of_le hx with hx0 | hxpos
    · rw [← hx0, Real.zero_rpow ha.ne']
      nlinarith
    · have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
      have hb := rpow_one_add_le_one_add_mul_self
        (by have : 0 ≤ y / x := div_nonneg hy0 hxpos.le; linarith : -1 ≤ y / x - 1) ha.le ha1
      rw [show 1 + (y / x - 1) = y / x by ring, Real.div_rpow hy0 hxpos.le] at hb
      have h1 : x * y ^ a ≤ x * x ^ a + a * x ^ a * (y - x) := by
        have h2 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ x * x ^ a)
        have e1 : x * x ^ a * (y ^ a / x ^ a) = x * y ^ a := by field_simp
        have e2 : x * x ^ a * (1 + a * (y / x - 1)) = x * x ^ a + a * x ^ a * (y - x) := by
          field_simp
        linarith
      have hxy' : x ^ a ≤ y ^ a := Real.rpow_le_rpow hx hxy ha.le
      have h3 : a * x ^ a * (y - x) ≤ a * y ^ a * (y - x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy' ha.le) (sub_nonneg.mpr hxy)
      have h4 : (1 + a) * (c₂ * y ^ a) ≤ 1 := by nlinarith
      have h5 : c₂ * (x * y ^ a) ≤ c₂ * (x * x ^ a + a * y ^ a * (y - x)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc₂.le
      have h6 : (1 + a) * (c₂ * y ^ a) * (y - x) ≤ 1 * (y - x) :=
        mul_le_mul_of_nonneg_right h4 (sub_nonneg.mpr hxy)
      linarith
  by_cases hy : c₂ * y ^ a ≤ 1 / 2
  · have hx' : c₂ * x ^ a ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy ha.le) hc₂.le) hy
    rw [min_eq_right hx', min_eq_right hy]
    exact key x y hx hxy hy
  · push Not at hy
    rw [min_eq_left hy.le]
    by_cases hx' : 1 / 2 ≤ c₂ * x ^ a
    · rw [min_eq_left hx']
      linarith
    · push Not at hx'
      rw [min_eq_right hx'.le]
      set z₀ := (1 / (2 * c₂)) ^ (1 / a) with hz₀
      have hz0 : 0 ≤ z₀ := Real.rpow_nonneg (by positivity) _
      have hz₀a : z₀ ^ a = 1 / (2 * c₂) := by
        rw [hz₀, ← Real.rpow_mul (by positivity), one_div_mul_cancel ha.ne', Real.rpow_one]
      have hcz : c₂ * z₀ ^ a = 1 / 2 := by
        rw [hz₀a]
        field_simp
      have hxz : x ≤ z₀ := by
        by_contra hlt
        push Not at hlt
        have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hz0 hlt ha) hc₂
        linarith
      have hzy : z₀ ≤ y := by
        by_contra hlt
        push Not at hlt
        have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (hx.trans hxy) hlt ha) hc₂
        linarith
      have h1 := key x z₀ hx hxz hcz.le
      rw [hcz] at h1
      linarith

theorem t0_eq' (M K : ℝ) (hM : 0 < M) (hK : 0 < K) :
    max (⌊Real.logb (1 - 1 / 2) (K / (M / 2))⌋ + 2) 1 =
      max (⌊Real.logb 2 (M / K)⌋ + 1) (1 : ℤ) := by
  have e : Real.logb (1 - 1 / 2) (K / (M / 2)) = Real.logb 2 (M / K) - 1 := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, show K / (M / 2) = 2 * K / M by field_simp]
    simp only [Real.logb, Real.log_inv]
    rw [Real.log_div (by positivity) hM.ne', Real.log_mul (by norm_num) hK.ne',
      Real.log_div hM.ne' hK.ne']
    field_simp
    ring
  rw [e, Int.floor_sub_one]
  congr 1
  ring

theorem sharp_away_sublinear : SharpAwaySublinear.{u} := by
  intro E _ _ V f L c δ θ x S lam hL hc hδ hθ0 hθ hsc hconv hsm hsharp hrun xStar hxs K t₀ t ht
  classical
  set D := Metric.diam (↑V : Set E) with hD
  have hKdef : K = (4 * c ^ 2 * L * D ^ 2 / δ ^ 2) ^ (1 / (1 - 2 * θ)) := rfl
  have ht0def : t₀ = max (⌊Real.logb 2 (L * D ^ 2 / K)⌋ + 1) 1 := rfl
  have ha0 : 0 < 1 - 2 * θ := by linarith
  have ha1 : 1 - 2 * θ ≤ 1 := by linarith
  have inv := Lemmata.AwayStepFW.Proof.run_inv (NNReal.coe_nonneg L) hrun
  have hxP : ∀ t, x t ∈ convexHull ℝ (↑V : Set E) := fun t =>
    convexHull_mono (by exact_mod_cast (inv t).sub) (inv t).mem_convexHull
  set h : ℕ → ℝ := fun t => f (x t) - f xStar with hh
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; linarith [hxs.2 _ (hxP t)]
  have hP : IsCompact (convexHull ℝ (↑V : Set E)) := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hdist : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D :=
    fun y hy z hz => by
      rw [← dist_eq_norm, hD, ← convexHull_diam]
      exact Metric.dist_le_diam_of_mem hP.isBounded hy hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ D from Metric.diam_nonneg) with hD0 | hDpos
  · have hxt : x t = xStar := by
      have h1 := hdist _ (hxP t) _ hxs.1
      rw [← hD0] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    have hK0 : K = 0 := by
      rw [hKdef, ← hD0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div]
      exact Real.zero_rpow (one_div_pos.mpr ha0).ne'
    have hht : f (x t) - f xStar = 0 := by rw [hxt, sub_self]
    rw [hht, hK0, ← hD0]
    constructor <;> intro _ <;> simp
  set a := 1 - 2 * θ with ha
  set c₂ := δ ^ 2 / (8 * c ^ 2 * L * D ^ 2) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set c₀ := (L : ℝ) * D ^ 2 / 2 with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set φ : ℝ → ℝ := fun z => z - z * min (1 / 2) (c₂ * z ^ a) with hφ
  have hφmono : ∀ y z, 0 ≤ y → y ≤ z → φ y ≤ φ z := fun y z hy hyz =>
    contraction_mono hc₂0 ha0 ha1 hy hyz
  have hφle : ∀ z, 0 ≤ z → φ z ≤ z := fun z hz => by
    have : 0 ≤ min (1 / 2) (c₂ * z ^ a) := le_min (by norm_num) (by positivity)
    simp only [hφ]
    nlinarith
  have hφnn : ∀ z, 0 ≤ z → 0 ≤ φ z := fun z hz => by
    have : min (1 / 2) (c₂ * z ^ a) ≤ 1 / 2 := min_le_left _ _
    simp only [hφ]
    nlinarith
  have hout : ∀ t, (h (t + 1) ≤ φ (h t) ∧ (S (t + 1)).card ≤ (S t).card + 1) ∨
      (h (t + 1) ≤ h t ∧ (S (t + 1)).card + 1 = (S t).card) := by
    intro t
    obtain ⟨v, hvV, hv, a', ha', haS, hstep⟩ := hrun.2.2.2 t
    rcases afw_step_progress hL hconv hsm hxs (inv t) hvV hv ha' haS hstep with
      ⟨h1, hc'⟩ | ⟨h1, hc'⟩
    · left
      refine ⟨?_, hc'⟩
      set h0 := f (x t) - f xStar with hh0def
      set gav := fderiv ℝ f (x t) (a' - v) with hgav
      have hm : h0 * min (1 / 2) (c₂ * h0 ^ a) ≤
          min (h0 / 2) (gav ^ 2 / (8 * (L * D ^ 2))) := by
        rcases eq_or_lt_of_le (hh0 t) with hz | hpos
        · have hz' : h0 = 0 := hz.symm
          rw [hz']
          simp only [zero_mul, zero_div]
          exact le_min le_rfl (by positivity)
        apply le_min
        · have := min_le_left (1 / 2 : ℝ) (c₂ * h0 ^ a)
          nlinarith
        · have hgeo := Proof.geometric_sharpness V f c θ δ hconv hsm.1 hc hδ hsc hsharp
            xStar hxs (S t) (inv t).sub (x t) (inv t).mem_convexHull (by linarith) a' ha' haS v
            hvV hv
          set r := h0 ^ (1 - θ) with hr
          have hr0 : 0 ≤ r := Real.rpow_nonneg hpos.le _
          have hr2 : r ^ 2 = h0 * h0 ^ a := by
            rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
              show (1 - θ) * ((2 : ℕ) : ℝ) = 1 + a by rw [ha]; push_cast; ring,
              Real.rpow_add hpos, Real.rpow_one]
          have h3 : r * δ ≤ gav * c := by
            rw [div_le_div_iff₀ hc hδ] at hgeo
            exact hgeo
          have h4 : 0 ≤ gav := by
            have := mul_nonneg hr0 hδ.le
            by_contra hneg
            push Not at hneg
            nlinarith
          have h5 : (r * δ) ^ 2 ≤ (gav * c) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
          rw [mul_pow, mul_pow, hr2] at h5
          calc h0 * min (1 / 2) (c₂ * h0 ^ a) ≤ h0 * (c₂ * h0 ^ a) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
            _ = δ ^ 2 * (h0 * h0 ^ a) / (8 * c ^ 2 * L * D ^ 2) := by rw [hc₂]; ring
            _ ≤ gav ^ 2 * c ^ 2 / (8 * c ^ 2 * L * D ^ 2) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                linarith
            _ = gav ^ 2 / (8 * (L * D ^ 2)) := by field_simp
      show h (t + 1) ≤ φ (h t)
      simp only [hh, hφ]
      linarith
    · right
      exact ⟨by simp only [hh]; linarith, hc'⟩
  let u : ℕ → ℝ := fun j => Nat.rec (motive := fun _ => ℝ) c₀ (fun _ y => φ y) j
  have hu0 : u 0 = c₀ := rfl
  have husucc : ∀ j, u (j + 1) = φ (u j) := fun j => rfl
  have hunn : ∀ j, 0 ≤ u j := by
    intro j
    induction j with
    | zero => exact hc₀0.le
    | succ j ih => rw [husucc]; exact hφnn _ ih
  have huanti : Antitone u :=
    antitone_nat_of_succ_le (fun j => by rw [husucc]; exact hφle _ (hunn j))
  have hstate : ∀ n, ∃ G Dr : ℕ, G + Dr = n ∧ (S (n + 1)).card + Dr ≤ (S 1).card + G ∧
      h (n + 1) ≤ u G := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, 0, rfl, le_rfl, ?_⟩
      rw [hu0]
      simpa [hh] using Lemmata.AwayStepFW.Proof.first_step_bound hL hconv hsm hxs hrun
    | succ n ih =>
      obtain ⟨G, Dr, hsum, hcard, hbd⟩ := ih
      rcases hout (n + 1) with ⟨h1, hc'⟩ | ⟨h1, hc'⟩
      · exact ⟨G + 1, Dr, by omega, by omega,
          h1.trans (by rw [husucc]; exact hφmono _ _ (hh0 _) hbd)⟩
      · exact ⟨G, Dr + 1, by omega, by omega, h1.trans hbd⟩
  have hS1 : (S 1).card ≤ 2 := by
    rcases hout 0 with ⟨-, hc'⟩ | ⟨-, hc'⟩ <;>
      simp only [zero_add, hrun.2.1, Finset.card_singleton] at hc' <;> omega
  obtain ⟨G, Dr, hsum, hcard, hbd⟩ := hstate (t - 1)
  rw [show t - 1 + 1 = t by omega] at hcard hbd
  have hSt : 1 ≤ (S t).card := by
    rcases Nat.eq_zero_or_pos (S t).card with h0 | h0
    · have := (inv t).sum
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at this
      norm_num at this
    · exact h0
  have hG : (t - 1) / 2 ≤ G := by omega
  have hht : h t ≤ u ((t - 1) / 2) := hbd.trans (huanti hG)
  set w : ℕ → ℝ := fun T => u (T - 1) with hw
  have hw1 : w 1 ≤ c₀ := le_of_eq hu0
  have hwmono : ∀ T, w (T + 1) ≤ w T := fun T => by
    simp only [hw, Nat.add_sub_cancel]
    exact huanti (Nat.sub_le T 1)
  have hwstep : ∀ T, 1 ≤ T → 0 < w T →
      w T * min (1 / 2) (c₂ * w T ^ a) ≤ w T - w (T + 1) := by
    intro T hT _
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    simp only [hw, Nat.add_sub_cancel, husucc, hφ]
    linarith
  have hRA := Lemmata.CGBasics.Proof.rate_assembly w c₀ c₂ a hc₀0 hc₂0 ha0 (fun T => hunn _)
    hwmono hw1 hwstep ((t - 1) / 2 + 1) (by omega)
  have hwT : w ((t - 1) / 2 + 1) = u ((t - 1) / 2) := by simp only [hw, Nat.add_sub_cancel]
  have hKpos : 0 < K := by rw [hKdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hKeq : (1 / 2 / c₂) ^ (1 / a) = K := by
    rw [hKdef, hc₂]
    congr 1
    field_simp
    ring
  have ht0eq : max (⌊Real.logb (1 - 1 / 2) (K / c₀)⌋ + 2) 1 = t₀ := by
    rw [ht0def, hc₀]
    exact t0_eq' _ K (by positivity) hKpos
  rw [hwT, hKeq, ht0eq] at hRA
  obtain ⟨hA, hB⟩ := hRA
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · calc h t ≤ u ((t - 1) / 2) := hht
      _ ≤ c₀ * (1 - 1 / 2) ^ ((t - 1) / 2 + 1 - 1) := hA hlt
      _ = L * D ^ 2 / 2 ^ ((t - 1) / 2 + 1) :=
        Lemmata.CGBasics.Proof.first_regime L D _ (by omega)
  · calc h t ≤ u ((t - 1) / 2) := hht
      _ ≤ K / (1 + 1 / 2 * a * ((((t - 1) / 2 + 1 : ℕ) : ℝ) - t₀)) ^ (1 / a) := hB hge
      _ = K / (1 + (1 / 2 - θ) * ((((t - 1) / 2 + 1 : ℕ) : ℝ) - t₀)) ^ (1 / a) := by
        rw [ha]
        ring_nf

theorem sharp_gradient_dominated : SharpGradientDominated.{u} := by
  intro E _ _ C f c θ hC hconv hdiff hc hθ hsharp xStar hxs x hx
  have hle : f xStar ≤ f x := hxs.2 x hx
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [← heq, sub_self, Real.zero_rpow (by linarith), zero_div]
    exact norm_nonneg _
  · obtain ⟨y, hy, hbound⟩ := sharp_primal_gap C f c θ hC hconv hdiff hc hsharp xStar hxs x hx hlt
    have hxy : x ≠ y := by
      rintro rfl
      have := hy.2 xStar hxs.1
      linarith
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    refine hbound.trans ?_
    rw [div_le_iff₀ hpos]
    have h1 := (fderiv ℝ f x).le_opNorm (x - y)
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1

end Proof

end Lemmata.CGImprovements
