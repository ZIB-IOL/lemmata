module

public import Lemmata.Centroid.Proof.General.LocalAverage

@[expose] public section

namespace Lemmata.Centroid.General

noncomputable section

def residueCost (r : ℝ) : ℝ := r ^ (2 / 3 : ℝ) + 2 * r ^ (1 / 3 : ℝ)

theorem cubeRoot_cube {r : ℝ} (hr : 0 ≤ r) : (r ^ (1 / 3 : ℝ)) ^ 3 = r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

theorem cubeRoot_square {r : ℝ} (hr : 0 ≤ r) : (r ^ (1 / 3 : ℝ)) ^ 2 = r ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

theorem cubeRoot_two_le {r : ℝ} (hr : 8 ≤ r) : 2 ≤ r ^ (1 / 3 : ℝ) := by
  have hroot := Real.rpow_nonneg (by linarith : 0 ≤ r) (1 / 3 : ℝ)
  have hcube := cubeRoot_cube (by linarith : 0 ≤ r)
  by_contra hn
  have hp := pow_lt_pow_left₀ (show r ^ (1 / 3 : ℝ) < 2 by linarith) hroot (by decide : 3 ≠ 0)
  norm_num at hp
  linarith

theorem residue_average_lower_root {r e t u m : ℝ}
    (ht : 2 ≤ t) (hr : r = t ^ 3) (he₂ : 2 ≤ e) (her : e ≤ r)
    (hu : t ^ 2 ≤ u) (hm : u + e * r / u ≤ m) : t ^ 2 + 2 * t + e - 2 ≤ m := by
  have ht0 : 0 ≤ t := by linarith
  have hu0 : 0 < u := by nlinarith
  have ht2 : 2 * t ≤ t ^ 2 := by nlinarith [mul_nonneg ht0 (show 0 ≤ t - 2 by linarith)]
  have hbase : u * (t ^ 2 + 2 * t) ≤ u ^ 2 + 2 * r := by
    have hp := mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u - 2 * t by linarith)
    nlinarith only [hp, hr]
  have hcost : t ^ 2 + 2 * t ≤ r := by
    have hp := mul_nonneg (mul_nonneg ht0 (show 0 ≤ t - 2 by linarith))
      (show 0 ≤ t + 1 by linarith)
    nlinarith only [hp, hr]
  have hbound : u * (t ^ 2 + 2 * t + e - 2) ≤ u ^ 2 + e * r := by
    by_cases hur : u ≤ r
    · have hp := mul_nonneg (show 0 ≤ e - 2 by linarith) (sub_nonneg.mpr hur)
      nlinarith only [hbase, hp]
    · have hp := mul_nonneg (show 0 ≤ r - e by linarith) (show 0 ≤ u - r by linarith)
      have hq := mul_nonneg hu0.le (show 0 ≤ r - (t ^ 2 + 2 * t) + 2 by linarith)
      nlinarith only [hp, hq, sq_nonneg (u - r)]
  have hle : t ^ 2 + 2 * t + e - 2 ≤ u + e * r / u := by
    have hdiv := div_mul_cancel₀ (e * r) hu0.ne'
    apply (mul_le_mul_iff_of_pos_right hu0).1
    nlinarith only [hbound, hdiv]
  exact hle.trans hm

theorem cubic_cost_lipschitz {t z : ℝ} (ht : 2 ≤ t) (htz : t ≤ z) :
    z ^ 2 + 2 * z ≤ t ^ 2 + 2 * t + (z ^ 3 - t ^ 3) := by
  have ht0 : 0 ≤ t := by linarith
  have hz0 : 0 ≤ z := by linarith
  have ht2 : t + 2 ≤ t ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ t - 2 by linarith) (show 0 ≤ t + 1 by linarith)]
  have hz2 : z ≤ z ^ 2 := by nlinarith [mul_nonneg hz0 (show 0 ≤ z - 1 by linarith)]
  have hq : 0 ≤ z ^ 2 + z * t + t ^ 2 - z - t - 2 := by nlinarith [mul_nonneg hz0 ht0]
  have hp := mul_nonneg (sub_nonneg.mpr htz) hq
  nlinarith only [hp]

theorem residueCost_shift {r δ : ℝ} (hr : 8 ≤ r) (hδ : 0 ≤ δ) :
    residueCost (r + δ) ≤ residueCost r + δ := by
  let t := r ^ (1 / 3 : ℝ)
  let z := (r + δ) ^ (1 / 3 : ℝ)
  have ht : 2 ≤ t := cubeRoot_two_le hr
  have htz : t ≤ z := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h := cubic_cost_lipschitz ht htz
  have htcube : t ^ 3 = r := cubeRoot_cube (by linarith)
  have hzcube : z ^ 3 = r + δ := cubeRoot_cube (by linarith)
  rw [htcube, hzcube, add_sub_cancel_left] at h
  simpa only [residueCost, ← cubeRoot_square (by linarith : 0 ≤ r),
    ← cubeRoot_square (by linarith : 0 ≤ r + δ), t, z] using h

theorem residue_average_lower {r e u m : ℝ} (hr : 8 ≤ r) (he₂ : 2 ≤ e) (her : e ≤ r)
    (hu : r ^ (2 / 3 : ℝ) ≤ u) (hm : u + e * r / u ≤ m) :
    residueCost (r + e - 2) ≤ m := by
  have hroot := residue_average_lower_root (cubeRoot_two_le hr)
    (cubeRoot_cube (by linarith : 0 ≤ r)).symm he₂ her
    (by simpa only [cubeRoot_square (by linarith : 0 ≤ r)] using hu) hm
  have hshift := residueCost_shift hr (show 0 ≤ e - 2 by linarith)
  rw [show r + (e - 2) = r + e - 2 by ring] at hshift
  apply hshift.trans
  simpa only [residueCost, cubeRoot_square (by linarith : 0 ≤ r), sub_eq_add_neg, add_assoc] using hroot

private theorem quadratic_root_le {z a N : ℝ} (ha : 0 ≤ a)
    (hb : z ^ 2 + 2 * z ≤ N) (hN : N ≤ a ^ 2 + 2 * a) : z ≤ a := by
  by_contra hn
  have hp := mul_pos (show 0 < z - a by linarith) (show 0 < z + a + 2 by linarith)
  nlinarith only [hb, hN, hp]

private theorem quadratic_root_lt {z a N : ℝ} (ha : 0 ≤ a)
    (hb : z ^ 2 + 2 * z ≤ N) (hN : N < a ^ 2 + 2 * a) : z < a := by
  by_contra hn
  have hp := mul_nonneg (show 0 ≤ z - a by linarith) (show 0 ≤ z + a + 2 by linarith)
  nlinarith only [hb, hN, hp]

private theorem root_bound_first {D N n s : ℕ} {z : ℝ} (hn : 0 < n) (hs : s ≤ n)
    (hN : N = n * (n + 1) + s) (hz : 0 ≤ z) (hcube : z ^ 3 = (D : ℝ) - 2)
    (hbudget : z ^ 2 + 2 * z ≤ N) : D ≤ generalBoundAt n s := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNreal : (N : ℝ) = (n : ℝ) * ((n : ℝ) + 1) + s := by exact_mod_cast hN
  have hsreal : (s : ℝ) ≤ n := by exact_mod_cast hs
  have hzn : z ≤ n := quadratic_root_le hn0 hbudget (by nlinarith)
  have hpow := pow_le_pow_left₀ hz hzn 3
  have hDle : D ≤ n ^ 3 + 2 := by exact_mod_cast (show (D : ℝ) ≤ (n : ℝ) ^ 3 + 2 by linarith)
  by_cases hs0 : s = 0
  · have hzlt : z < n := quadratic_root_lt hn0 hbudget (by simp only [hs0, Nat.cast_zero] at hNreal; nlinarith)
    have hp := pow_lt_pow_left₀ hzlt hz (by decide : 3 ≠ 0)
    have hDlt : D < n ^ 3 + 2 := by exact_mod_cast (show (D : ℝ) < (n : ℝ) ^ 3 + 2 by linarith)
    rw [hs0, generalBoundAt_zero]
    omega
  · by_cases hs1 : s = 1
    · simpa only [hs1, generalBoundAt_one] using hDle
    · rw [generalBoundAt, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs]
      have hprod : 2 ≤ s * (s - 1) := by
        exact (by norm_num : 2 ≤ 2 * 1).trans (Nat.mul_le_mul (by omega) (by omega))
      omega

private theorem root_second_cubic {N n s : ℕ} {z : ℝ} (hn : 0 < n)
    (hs : n < s) (hsmax : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s)
    (hz : 0 ≤ z) (hbudget : z ^ 2 + 2 * z ≤ N) : z ^ 3 < (n : ℝ) * ((N : ℝ) - n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNreal : (N : ℝ) = (n : ℝ) * ((n : ℝ) + 1) + s := by exact_mod_cast hN
  have hslo : (n : ℝ) + 1 ≤ s := by exact_mod_cast hs
  have hshi : (s : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hsmax
  by_cases hzn : z ≤ n
  · have hpow := pow_le_pow_left₀ hz hzn 3
    have hlow : (n : ℝ) ^ 2 + 2 * n + 1 ≤ N := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlow hn0
    nlinarith
  · have hhalf : z < (n : ℝ) + 1 / 2 := quadratic_root_lt (by positivity) hbudget (by nlinarith)
    let δ := z - (n : ℝ)
    have hδ0 : 0 ≤ δ := by dsimp only [δ]; linarith
    have hδhalf : δ < 1 / 2 := by dsimp only [δ]; linarith
    have h₁ := mul_le_mul_of_nonneg_left (show δ - 1 ≤ -(1 / 2 : ℝ) by linarith) (sq_nonneg (n : ℝ))
    have h₂ : 2 * (n : ℝ) * δ * (δ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h₃ : δ ^ 3 < 1 / 8 := by
      have hp := pow_lt_pow_left₀ hδhalf hδ0 (by decide : 3 ≠ 0)
      norm_num at hp
      exact hp
    have hsum : (n : ℝ) ^ 2 * (δ - 1) + 2 * n * δ * (δ - 1) + δ ^ 3 < 0 := by
      nlinarith only [h₁, h₂, h₃, hn1, sq_nonneg ((n : ℝ) - 1)]
    have heq : z ^ 3 - (n : ℝ) * (z ^ 2 + 2 * z - n) =
        (n : ℝ) ^ 2 * (δ - 1) + 2 * n * δ * (δ - 1) + δ ^ 3 := by dsimp only [δ]; ring
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hbudget (n : ℝ)) hn0
    nlinarith only [hsum, heq, hmul]

theorem residue_root_dimension_bound_at {D N n s : ℕ} {z : ℝ} (hn : 0 < n)
    (hs : s ≤ 2 * n + 1) (hN : N = n * (n + 1) + s) (hz : 0 ≤ z)
    (hcube : z ^ 3 = (D : ℝ) - 2) (hbudget : z ^ 2 + 2 * z ≤ N) : D ≤ generalBoundAt n s := by
  by_cases hsn : s ≤ n
  · exact root_bound_first hn hsn hN hz hcube hbudget
  · have hroot := root_second_cubic hn (by omega) hs hN hz hbudget
    have hnN : n ≤ N := by nlinarith
    have hDreal : (D : ℝ) < (n : ℝ) * ((N - n : ℕ) : ℝ) + 2 := by
      rw [Nat.cast_sub hnN]
      linarith
    have hDlt : D < n * (N - n) + 2 := by exact_mod_cast hDreal
    let t := s - n - 1
    have hsEq : s = n + 1 + t := by dsimp only [t]; omega
    have hNsub : N - n = n ^ 2 + n + t + 1 := by
      have heq : N = n + (n ^ 2 + n + t + 1) := by nlinarith
      rw [heq, Nat.add_sub_cancel_left]
    have hpred := generalBoundAt_second_pred n t hn
    have hmax := le_max_left n (t ^ 2)
    have hMpos : 0 < generalBoundAt n (n + 1 + t) := by rw [generalBoundAt_second hn]; omega
    have hM : generalBoundAt n (n + 1 + t) = n * (n ^ 2 + n + t) + max n (t ^ 2) + 1 := by omega
    rw [hsEq]
    rw [hNsub] at hDlt
    rw [hM]
    nlinarith only [hDlt, hmax]

theorem residue_cost_dimension_bound (D N : ℕ) (hD : 10 ≤ D)
    (hcost : residueCost ((D : ℝ) - 2) ≤ N) : D ≤ generalBound N := by
  let z := ((D : ℝ) - 2) ^ (1 / 3 : ℝ)
  have hDreal : (10 : ℝ) ≤ D := by exact_mod_cast hD
  have hr : 8 ≤ (D : ℝ) - 2 := by linarith
  have hz : 2 ≤ z := cubeRoot_two_le hr
  have hc : z ^ 3 = (D : ℝ) - 2 := cubeRoot_cube (by linarith)
  have hb : z ^ 2 + 2 * z ≤ N := by
    simpa only [residueCost, ← cubeRoot_square (by linarith : 0 ≤ (D : ℝ) - 2)] using hcost
  have hNreal : (2 : ℝ) ≤ N := by nlinarith
  have hN : 2 ≤ N := by exact_mod_cast hNreal
  have hs := general_remainder_le hN
  have hdecomp := general_decomposition N
  rw [generalBound_eq hN hs hdecomp]
  exact residue_root_dimension_bound_at (generalIndex_pos hN) hs hdecomp (by linarith) hc hb

theorem residueCost_le_self {r : ℝ} (hr : 8 ≤ r) : residueCost r ≤ r := by
  let t := r ^ (1 / 3 : ℝ)
  have ht : 2 ≤ t := cubeRoot_two_le hr
  have hc : t ^ 3 = r := cubeRoot_cube (by linarith)
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t - 2 by linarith))
    (show 0 ≤ t + 1 by linarith)
  have hz : t ^ 2 + 2 * t ≤ r := by nlinarith only [hp, hc]
  simpa only [residueCost, ← cubeRoot_square (by linarith : 0 ≤ r), t] using hz

theorem le_generalBound (N : ℕ) : N ≤ generalBound N := by
  by_cases hN : N < 10
  · have hs : ∀ n : Fin 10, n.val ≤ generalBound n.val := by decide
    exact hs ⟨N, hN⟩
  · have hN10 : 10 ≤ N := by omega
    apply residue_cost_dimension_bound N N hN10
    have hn : (10 : ℝ) ≤ N := by exact_mod_cast hN10
    exact (residueCost_le_self (by linarith : 8 ≤ (N : ℝ) - 2)).trans (by linarith)

theorem dimensionCost_le_of_residueCost {D : ℕ} {m : ℝ} (hD : 10 ≤ D)
    (hcost : residueCost ((D : ℝ) - 2) ≤ m) : dimensionCost D ≤ m := by
  have hdreal : (10 : ℝ) ≤ D := by exact_mod_cast hD
  have hroot := cubeRoot_two_le (by linarith : 8 ≤ (D : ℝ) - 2)
  have hinc := dimensionCost_increment_anti (show 0 ≤ D - 1 by omega)
  dsimp only at hinc
  rw [show D - 1 + 1 = D by omega, zero_add, dimensionCost_one, dimensionCost_zero, sub_zero] at hinc
  have hpred : dimensionCost (D - 1) = supportCost ((D : ℝ) - 2) := by
    rw [dimensionCost, ite_eq_right (by omega), Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
    congr 1
    ring
  rw [hpred] at hinc
  dsimp only [residueCost, supportCost] at hcost hinc
  linarith

theorem dimensionCost_le_self (D : ℕ) : dimensionCost D ≤ D := by
  induction D with
  | zero => simp
  | succ D ih =>
    have h := dimensionCost_add D 1
    rw [dimensionCost_one] at h
    have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by norm_num
    rw [hcast]
    linarith

private theorem twice_le_of_dvd {e k : ℕ} (hk : 0 < k) (hdiv : e ∣ k)
    (hne : k ≠ e) : 2 * e ≤ k := by
  obtain ⟨a, rfl⟩ := hdiv
  have ha : 2 ≤ a := by
    by_contra hn
    have ha : a = 0 ∨ a = 1 := by omega
    rcases ha with ha | ha <;> simp [ha] at hk hne
  nlinarith

theorem residue_profile_dichotomy (D e r : ℕ) (k q m : Fin 3 → ℕ)
    (he : 2 ≤ e) (hdim : D = e + r) (hDdiv : e ∣ D)
    (hkdiv : ∀ i, e ∣ k i) (hqdiv : ∀ i, e ∣ q i)
    (hm : ∀ i, m i = k i + q i) (hformat : ∀ i, 0 < m i)
    (hbound : ∀ i, r * e ≤ k i * q i) (hprod : r ^ 2 ≤ q 0 * q 1 * q 2) :
    (∀ i, D ≤ m i) ∨ (10 ≤ D ∧ residueCost ((D : ℝ) - 2) ≤
      ((m 0 : ℝ) + m 1 + m 2) / 3) := by
  by_cases hall : ∀ i, D ≤ m i
  · exact Or.inl hall
  right
  obtain ⟨i, hi⟩ := not_forall.mp hall
  have him : m i < D := Nat.lt_of_not_ge hi
  have hepos : 0 < e := by omega
  have hrpos : 0 < r := by
    by_contra hn
    have hr : r = 0 := by omega
    have hdiv : e ∣ m i := by rw [hm]; exact dvd_add (hkdiv i) (hqdiv i)
    have hle := Nat.le_of_dvd (hformat i) hdiv
    omega
  have hRpos : 0 < r * e := Nat.mul_pos hrpos hepos
  have hkpos (j : Fin 3) : 0 < k j := by
    have hb := hbound j
    by_contra hn
    have hz : k j = 0 := by omega
    rw [hz, zero_mul] at hb
    omega
  have hqpos (j : Fin 3) : 0 < q j := by
    have hb := hbound j
    by_contra hn
    have hz : q j = 0 := by omega
    rw [hz, mul_zero] at hb
    omega
  have hkne : k i ≠ e := by
    intro heq
    have hb := hbound i
    rw [heq] at hb
    have hrq : r ≤ q i := by nlinarith
    have hm' := hm i
    omega
  have hqne : q i ≠ e := by
    intro heq
    have hb := hbound i
    rw [heq] at hb
    have hrk : r ≤ k i := by nlinarith
    have hm' := hm i
    omega
  have hk2 := twice_le_of_dvd (hkpos i) (hkdiv i) hkne
  have hq2 := twice_le_of_dvd (hqpos i) (hqdiv i) hqne
  have hD4 : 4 * e < D := by have hmi := hm i; omega
  have hD5 : 5 * e ≤ D := by
    obtain ⟨a, ha⟩ := hDdiv
    have ha5 : 5 ≤ a := by nlinarith
    nlinarith
  have hr8 : 8 ≤ r := by omega
  have her : e ≤ r := by omega
  refine ⟨by omega, ?_⟩
  have hqR (j : Fin 3) : (0 : ℝ) < q j := by exact_mod_cast hqpos j
  have hmR (j : Fin 3) : (q j : ℝ) + (e : ℝ) * r / q j ≤ m j := by
    have hb : (e : ℝ) * r ≤ (k j : ℝ) * q j := by
      exact_mod_cast (by simpa only [mul_comm] using hbound j : e * r ≤ k j * q j)
    have hdiv := (div_le_iff₀ (hqR j)).2 hb
    have hm' : (m j : ℝ) = (k j : ℝ) + q j := by exact_mod_cast hm j
    linarith
  have hmean := geometric_mean3_module_bound (by positivity : (0 : ℝ) ≤ (e : ℝ) * r)
    (hqR 0) (hqR 1) (hqR 2) (hmR 0) (hmR 1) (hmR 2)
  have hpR : (r : ℝ) ^ 2 ≤ (q 0 : ℝ) * q 1 * q 2 := by exact_mod_cast hprod
  have hroot := Real.rpow_le_rpow (sq_nonneg (r : ℝ)) hpR (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)] at hroot
  norm_num at hroot
  have hcost := residue_average_lower (by exact_mod_cast hr8) (by exact_mod_cast he)
    (by exact_mod_cast her) hroot hmean
  have hdR : (D : ℝ) = (r : ℝ) + e := by exact_mod_cast (by omega : D = r + e)
  simpa only [← hdR] using hcost

end

end Lemmata.Centroid.General
