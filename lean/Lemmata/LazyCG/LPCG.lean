module

public import Lemmata.LazyCG.Statement
public import Lemmata.AwayStepFW.SimplexLike

@[expose] public section

/-!
# Lazy pairwise conditional gradients (Theorem 3.2)

Step sizes that are powers of `1/2` keep the iterates on a dyadic grid, hence in `P`. A negative
answer bounds `f'(x_t)(a - v)` by `Φ_t/Δ_t` for the away vertex `a` and the Frank–Wolfe vertex `v`;
with sparsity scaling and strong convexity at `x_t` this gives `h_t ≤ ‖x⋆‖₀ Φ_t²/(2 S Δ_t²) ≤ Φ_t`.
A positive answer gains `η̃_t Φ_t/(K Δ_t)`, which the definition of `Φ_t` accounts for.
-/

namespace Lemmata.LazyCG

open Lemmata.FrankWolfe Lemmata.AwayStepFW.Proof

namespace Proof

variable {n : ℕ}

/-- Feasibility on a dyadic grid, for steps that either stay or move by `η'_t (u - w)` with the
support of `w` inside that of `x_t`. -/
theorem lpcg_feasible {V : Finset (EuclideanSpace ℝ (Fin n))}
    {W : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))}
    (hP : convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) = {x | ∀ i, 0 ≤ x i} ∩ (W : Set _))
    (h01 : ∀ v ∈ V, ∀ i, v i = 0 ∨ v i = 1) {x : ℕ → EuclideanSpace ℝ (Fin n)} {η' : ℕ → ℝ}
    (hx1 : x 1 ∈ V) (hdy : ∀ t, 1 ≤ t → ∃ δ : ℕ, η' t = (1 / 2) ^ δ)
    (hmono : ∀ t, 1 ≤ t → η' (t + 1) ≤ η' t)
    (hstep : ∀ t, 1 ≤ t → x (t + 1) = x t ∨ ∃ u ∈ V, ∃ w ∈ V, (∀ i, x t i = 0 → w i = 0) ∧
      x (t + 1) = x t + η' t • (u - w)) :
    ∀ t, 1 ≤ t → x t ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) ∧
      ∀ i, ∃ s : ℕ, x t i = η' t * s := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    refine ⟨subset_convexHull ℝ _ (by exact_mod_cast hx1), fun i => ?_⟩
    obtain ⟨m, hm⟩ := hdy 1 le_rfl
    rcases h01 _ hx1 i with h | h
    · exact ⟨0, by rw [h]; simp⟩
    · refine ⟨2 ^ m, ?_⟩
      rw [h, hm]
      push_cast
      rw [← mul_pow]
      norm_num
  | succ t ht ih =>
    obtain ⟨hxt, hs⟩ := ih
    obtain ⟨m, hm⟩ := hdy t ht
    obtain ⟨m', hm'⟩ := hdy (t + 1) (by omega)
    have hmm : m ≤ m' := by
      have := hmono t ht
      rw [hm, hm'] at this
      exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mp this
    obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
    have h2 : ((1 : ℝ) / 2) ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
    have hregrid : ∀ s : ℕ, η' t * s = η' (t + 1) * (2 ^ d * s : ℕ) := fun s => by
      rw [hm, hm']
      push_cast
      calc ((1 : ℝ) / 2) ^ m * s = (1 / 2) ^ m * ((1 / 2) ^ d * 2 ^ d) * s := by rw [h2, mul_one]
        _ = (1 / 2) ^ (m + d) * (2 ^ d * s) := by rw [pow_add]; ring
    rcases hstep t ht with hx' | ⟨u, huV, w, hwV, hwsupp, hx'⟩
    · rw [hx']
      refine ⟨hxt, fun i => ?_⟩
      obtain ⟨s, hsi⟩ := hs i
      exact ⟨2 ^ d * s, by rw [hsi, hregrid]⟩
    · have hcoord : ∀ i, ∃ s : ℕ, x (t + 1) i = η' t * s := fun i => by
        obtain ⟨s, hsi⟩ := hs i
        have hxi : x (t + 1) i = x t i + η' t * (u i - w i) := by rw [hx']; simp
        rcases h01 u huV i with hu | hu <;> rcases h01 w hwV i with hw | hw
        · exact ⟨s, by rw [hxi, hsi, hu, hw]; ring⟩
        · have hs1 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with h0 | h0
            · exfalso
              have := hwsupp i (by rw [hsi, h0]; simp)
              rw [hw] at this
              norm_num at this
            · exact h0
          exact ⟨s - 1, by rw [hxi, hsi, hu, hw, Nat.cast_sub hs1]; push_cast; ring⟩
        · exact ⟨s + 1, by rw [hxi, hsi, hu, hw]; push_cast; ring⟩
        · exact ⟨s, by rw [hxi, hsi, hu, hw]; ring⟩
      refine ⟨?_, fun i => ?_⟩
      · rw [hP]
        refine ⟨fun i => ?_, ?_⟩
        · obtain ⟨s, hsi⟩ := hcoord i
          rw [hsi, hm]
          positivity
        · rw [hx']
          have hxW := hull_mem_W hP hxt
          have huW := hull_mem_W hP (subset_convexHull ℝ _ (by exact_mod_cast huV))
          have hwW := hull_mem_W hP (subset_convexHull ℝ _ (by exact_mod_cast hwV))
          have h1 : η' t • (u -ᵥ w) +ᵥ x t ∈ W := AffineSubspace.vadd_mem_of_mem_direction
            (Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction huW hwW)) hxW
          simpa [vsub_eq_sub, vadd_eq_add, add_comm] using h1
      · obtain ⟨s, hsi⟩ := hcoord i
        exact ⟨2 ^ d * s, by rw [hsi, hregrid]⟩

theorem half_pow_le_of_lt {a b : ℕ} (h : ((1 : ℝ) / 2) ^ a < 2 * (1 / 2) ^ b) :
    ((1 : ℝ) / 2) ^ a ≤ (1 / 2) ^ b := by
  by_contra hlt
  push Not at hlt
  have hab : a < b := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mp hlt
  have h2 : ((1 : ℝ) / 2) ^ b ≤ (1 / 2) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
  rw [pow_succ] at h2
  linarith

set_option maxHeartbeats 1000000 in
theorem lpcg_rate : LPCGRate := by
  intro n V f K C S α x Φ η' hV hcurv hstrong hS hC hK hα hΦ0 xStar hxs hk h1 hrun
  classical
  obtain ⟨h01, W, hP⟩ := hV
  have hVnn : ∀ u ∈ V, ∀ i, 0 ≤ u i := fun u hu i => by
    rcases h01 u hu i with h | h <;> simp [h]
  set M₁ := √(S / (8 * α)) with hM₁
  set κ := min (M₁ / (K * C)) (1 / √(Φ 0)) with hκ
  have hK0 : 0 < K := by linarith
  have hM₁pos : 0 < M₁ := Real.sqrt_pos.mpr (by positivity)
  have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
  have hκ1 : κ ≤ M₁ / (K * C) := min_le_left _ _
  have hκ2 : κ ≤ 1 / √(Φ 0) := min_le_right _ _
  set B := κ * M₁ / (2 * K) with hB
  have hB0 : 0 < B := by positivity
  set r := (1 + κ ^ 2 * C / 2) / (1 + κ * M₁ / K) with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r ≤ (1 + B) / (1 + 2 * B) := by
    have h1' : κ ^ 2 * C / 2 ≤ B := by
      have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < K * C)).mp hκ1
      rw [hB, le_div_iff₀ (by positivity)]
      nlinarith
    have h2' : κ * M₁ / K = 2 * B := by rw [hB]; field_simp
    rw [hr, h2']
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hρ0 : 0 ≤ (1 + B) / (1 + 2 * B) := by positivity
  have hρ1 : (1 + B) / (1 + 2 * B) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hr1 : r ≤ 1 := hrρ.trans hρ1
  have hsq : M₁ * √(2 * α / S) = 1 / 2 := by
    rw [hM₁, ← Real.sqrt_mul (by positivity)]
    rw [show S / (8 * α) * (2 * α / S) = (1 / 2) ^ 2 by field_simp; norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hq0 : 0 < √(2 * α / S) := Real.sqrt_pos.mpr (by positivity)
  have hΔeq : ∀ φ : ℝ, 0 ≤ φ → √(2 * α * φ / S) = √(2 * α / S) * √φ := fun φ hφ => by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  -- the recursion for `Φ`
  have hrec : ∀ t, 1 ≤ t → 0 < Φ (t - 1) → Φ t = Φ (t - 1) * r := by
    intro t ht hpos
    rw [(hrun.2 t ht).1]
    have hp' : 0 < √(Φ (t - 1)) := Real.sqrt_pos.mpr hpos
    have hs1 : (κ * √(Φ (t - 1))) ^ 2 = κ ^ 2 * Φ (t - 1) := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
    have hs3 : κ * √(Φ (t - 1)) / (2 * K * √(2 * α * Φ (t - 1) / S)) = κ * M₁ / K := by
      rw [hΔeq _ hpos.le, div_eq_iff (by positivity)]
      calc κ * √(Φ (t - 1)) = κ * √(Φ (t - 1)) * (2 * (M₁ * √(2 * α / S))) := by
            rw [hsq]; ring
        _ = κ * M₁ / K * (2 * K * (√(2 * α / S) * √(Φ (t - 1)))) := by
            field_simp
    rw [hs1, hs3, hr]
    field_simp
  have hΦpos : ∀ t, 0 < Φ t := by
    intro t
    induction t with
    | zero => exact hΦ0
    | succ t ih =>
      rw [hrec (t + 1) (by omega) (by simpa using ih), Nat.add_sub_cancel]
      positivity
  have hrec' : ∀ t, 1 ≤ t → Φ t = Φ (t - 1) * r := fun t ht => hrec t ht (hΦpos _)
  have hΦle : ∀ t, Φ t ≤ Φ 0 * ((1 + B) / (1 + 2 * B)) ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hrec' (t + 1) (by omega), Nat.add_sub_cancel, pow_succ]
      calc Φ t * r ≤ Φ 0 * ((1 + B) / (1 + 2 * B)) ^ t * ((1 + B) / (1 + 2 * B)) :=
            mul_le_mul ih hrρ hr0.le (by have := hΦpos 0; positivity)
        _ = _ := by ring
  have hΦmono : ∀ t, 1 ≤ t → Φ t ≤ Φ (t - 1) := fun t ht => by
    rw [hrec' t ht]
    nlinarith [hΦpos (t - 1)]
  have hΦle0 : ∀ t, Φ t ≤ Φ 0 := fun t =>
    (hΦle t).trans (mul_le_of_le_one_right hΦ0.le (pow_le_one₀ hρ0 hρ1))
  have hη1 : ∀ t, κ * √(Φ t) ≤ 1 := fun t => by
    have h2 : √(Φ t) ≤ √(Φ 0) := Real.sqrt_le_sqrt (hΦle0 t)
    have h3 : 0 < √(Φ 0) := Real.sqrt_pos.mpr hΦ0
    calc κ * √(Φ t) ≤ 1 / √(Φ 0) * √(Φ 0) :=
          mul_le_mul hκ2 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = 1 := by field_simp
  -- dyadic step sizes
  have hdy : ∀ t, 1 ≤ t → ∃ δ : ℕ, η' t = (1 / 2) ^ δ := fun t ht => (hrun.2 t ht).2.1
  have hη'mono : ∀ t, 1 ≤ t → η' (t + 1) ≤ η' t := fun t ht => by
    obtain ⟨a, ha⟩ := hdy (t + 1) (by omega)
    obtain ⟨b, hb⟩ := hdy t ht
    have h2 := (hrun.2 (t + 1) (by omega)).2.2.1
    have h3 := (hrun.2 t ht).2.2.2.1
    rw [Nat.add_sub_cancel] at h2
    have h4 : κ * √(Φ t) ≤ κ * √(Φ (t - 1)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hΦmono t ht)) hκpos.le
    rw [ha, hb]
    apply half_pow_le_of_lt
    rw [← ha, ← hb]
    linarith
  have hstep : ∀ t, 1 ≤ t → x (t + 1) = x t ∨ ∃ u ∈ V, ∃ w ∈ V,
      (∀ i, x t i = 0 → w i = 0) ∧ x (t + 1) = x t + η' t • (u - w) := fun t ht => by
    rcases (hrun.2 t ht).2.2.2.2 with ⟨u, hu, w, hw, hws, -, hx'⟩ | ⟨-, hx'⟩
    · exact Or.inr ⟨u, hu, w, hw, hws, hx'⟩
    · exact Or.inl hx'
  have hfeas := lpcg_feasible hP h01 hrun.1 hdy hη'mono hstep
  have hxP : ∀ t, 1 ≤ t → x t ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) :=
    fun t ht => (hfeas t ht).1
  set k := (Finset.univ.filter fun i => xStar i ≠ 0).card with hkdef
  -- the main induction
  have hmain : ∀ t, f (x (t + 1)) - f xStar ≤ Φ t := by
    intro t
    induction t with
    | zero => simpa using h1
    | succ t ih =>
      have ht : 1 ≤ t + 1 := by omega
      obtain ⟨hΦdef, -, hη'le, hη'gt, hans⟩ := hrun.2 (t + 1) ht
      rw [Nat.add_sub_cancel] at hΦdef hη'le hη'gt hans
      set η := κ * √(Φ t) with hη
      set Δ := √(2 * α * Φ t / S) with hΔ
      have hΔpos : 0 < Δ := Real.sqrt_pos.mpr (by have := hΦpos t; positivity)
      have hΔ2 : Δ ^ 2 = 2 * α * Φ t / S := Real.sq_sqrt (by have := hΦpos t; positivity)
      have hη0 : 0 ≤ η := by positivity
      have hdef : Φ (t + 1) * (1 + η / (2 * K * Δ)) = Φ t + η ^ 2 * C / 2 := by
        rw [hΦdef, div_mul_cancel₀ _ (by positivity)]
      rcases hans with ⟨u, hu, w, hw, hws, hgt, hx'⟩ | ⟨hcert, hx'⟩
      · -- positive answer
        have hη'0 : 0 < η' (t + 1) := by
          obtain ⟨δ, hδ⟩ := hdy (t + 1) ht
          rw [hδ]
          positivity
        have hη'1 : η' (t + 1) ≤ 1 := hη'le.trans (hη1 t)
        have hc := hcurv (x (t + 1)) (hxP (t + 1) ht) u (by exact_mod_cast hu) w
          (by exact_mod_cast hw) (η' (t + 1)) ⟨hη'0.le, hη'1⟩
          (by rw [← hx']; exact hxP _ (by omega))
        rw [← hx'] at hc
        have hg : fderiv ℝ f (x (t + 1)) (u - w) = -fderiv ℝ f (x (t + 1)) (w - u) := by
          rw [← map_neg, neg_sub]
        rw [hg] at hc
        have hq : 0 ≤ Φ (t + 1) / (K * Δ) := by have := hΦpos (t + 1); positivity
        have h2 : η / 2 * (Φ (t + 1) / (K * Δ)) ≤ η' (t + 1) * fderiv ℝ f (x (t + 1)) (w - u) :=
          calc η / 2 * (Φ (t + 1) / (K * Δ)) ≤ η' (t + 1) * (Φ (t + 1) / (K * Δ)) :=
                mul_le_mul_of_nonneg_right (by linarith) hq
            _ ≤ _ := mul_le_mul_of_nonneg_left hgt.le hη'0.le
        have h3 : C / 2 * η' (t + 1) ^ 2 ≤ C / 2 * η ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη'0.le hη'le 2) (by positivity)
        have h4 : η / 2 * (Φ (t + 1) / (K * Δ)) = Φ (t + 1) * (η / (2 * K * Δ)) := by
          field_simp
        nlinarith
      · -- negative answer
        rw [hx']
        set g := fderiv ℝ f (x (t + 1)) with hg
        have hxt := hxP (t + 1) ht
        obtain ⟨lam, hlam0, hlam1, hxeq⟩ := Finset.mem_convexHull'.mp hxt
        have hne : (V.filter fun w => ∀ i, x (t + 1) i = 0 → w i = 0).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have hzero : ∀ w ∈ V, lam w = 0 := fun w hw => by
            by_contra hlw
            have hpos : 0 < lam w := lt_of_le_of_ne (hlam0 w hw) (Ne.symm hlw)
            have hmem : w ∈ V.filter fun w => ∀ i, x (t + 1) i = 0 → w i = 0 :=
              Finset.mem_filter.mpr ⟨hw, fun i hi =>
                support_sub_of_sum hVnn hlam0 hw hpos i (by rw [hxeq]; exact hi)⟩
            rw [hemp] at hmem
            exact absurd hmem (Finset.notMem_empty _)
          rw [Finset.sum_congr rfl hzero] at hlam1
          simp at hlam1
        obtain ⟨a, haF, hamax⟩ :=
          (V.filter fun w => ∀ i, x (t + 1) i = 0 → w i = 0).exists_max_image g hne
        have haV : a ∈ V := (Finset.mem_filter.mp haF).1
        have hasupp : ∀ i, x (t + 1) i = 0 → a i = 0 := (Finset.mem_filter.mp haF).2
        obtain ⟨v, hvV, hvmin⟩ := V.exists_min_image g ⟨x 1, hrun.1⟩
        have hsc := sparsity_scaling n V ⟨h01, W, hP⟩ (x (t + 1)) hxt xStar hxs.1 g a v haV
          hasupp (fun w hw hws => hamax w (Finset.mem_filter.mpr ⟨hw, hws⟩)) hvV hvmin
        have hcert' := hcert v (subset_convexHull ℝ _ (by exact_mod_cast hvV)) a
          (subset_convexHull ℝ _ (by exact_mod_cast haV)) hasupp
        have hsx := hstrong (x (t + 1)) hxt xStar hxs.1
        set rr := ‖x (t + 1) - xStar‖ with hrr
        have hrr' : ‖xStar - x (t + 1)‖ = rr := by rw [hrr, norm_sub_rev]
        rw [hrr'] at hsx
        have hgx : g (x (t + 1) - xStar) = -g (xStar - x (t + 1)) := by
          rw [← map_neg, neg_sub]
        set sk := √(k : ℝ) with hsk
        have hsk0 : 0 ≤ sk := Real.sqrt_nonneg _
        have hsk2 : sk ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg _)
        have hrr0 : 0 ≤ rr := norm_nonneg _
        have hkey : f (x (t + 1)) - f xStar + S / 2 * rr ^ 2 ≤ sk * rr * (Φ (t + 1) / Δ) := by
          have h2 : sk * rr * g (a - v) ≤ sk * rr * (Φ (t + 1) / Δ) :=
            mul_le_mul_of_nonneg_left hcert' (mul_nonneg hsk0 hrr0)
          rw [← hg] at hsx
          linarith
        set s' := sk * (Φ (t + 1) / Δ) with hs'
        have hamgm : rr * s' ≤ S / 2 * rr ^ 2 + s' ^ 2 / (2 * S) := by
          have e : S / 2 * rr ^ 2 + s' ^ 2 / (2 * S) - rr * s' = (S * rr - s') ^ 2 / (2 * S) := by
            field_simp
            ring
          have : 0 ≤ (S * rr - s') ^ 2 / (2 * S) := by positivity
          linarith
        have hh : f (x (t + 1)) - f xStar ≤ s' ^ 2 / (2 * S) := by
          have : sk * rr * (Φ (t + 1) / Δ) = rr * s' := by rw [hs']; ring
          linarith
        have hs'2 : s' ^ 2 / (2 * S) = k * Φ (t + 1) ^ 2 / (4 * α * Φ t) := by
          rw [hs', mul_pow, div_pow, hsk2, hΔ2]
          field_simp
          ring
        have hfin : k * Φ (t + 1) ^ 2 / (4 * α * Φ t) ≤ Φ (t + 1) := by
          have hΦt := hΦpos t
          have hΦt1 := hΦpos (t + 1)
          rw [div_le_iff₀ (by positivity)]
          have h2 : Φ (t + 1) ≤ Φ t := by simpa using hΦmono (t + 1) ht
          have h3 : (k : ℝ) * Φ (t + 1) ≤ α * Φ t :=
            mul_le_mul hk h2 hΦt1.le hα.le
          nlinarith
        linarith
  exact fun t => ⟨hmain t, hΦle t⟩

end Proof

end Lemmata.LazyCG
