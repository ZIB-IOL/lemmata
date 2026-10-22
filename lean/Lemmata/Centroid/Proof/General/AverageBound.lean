module

public import Lemmata.Centroid.Proof.General.CommonTail
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Lemmata.Centroid.General

def envelopeRoot (t : ℝ) : ℝ := (Real.sqrt (4 * t + 1) - 1) / 2
def envelope (t : ℝ) : ℝ := envelopeRoot t ^ 3

theorem envelopeRoot_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ envelopeRoot t := by
  have h : (1 : ℝ) ≤ Real.sqrt (4 * t + 1) :=
    (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  dsimp [envelopeRoot]
  linarith

theorem envelopeRoot_equation {t : ℝ} (ht : 0 ≤ t) :
    envelopeRoot t ^ 2 + envelopeRoot t = t := by
  have h := Real.sq_sqrt (show 0 ≤ 4 * t + 1 by linarith)
  dsimp [envelopeRoot]
  nlinarith

theorem envelope_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ envelope t :=
  pow_nonneg (envelopeRoot_nonneg ht) _

theorem envelope_equation {t : ℝ} (ht : 0 ≤ t) :
    envelope t ^ 2 + (3 * t + 1) * envelope t = t ^ 3 := by
  have h := envelopeRoot_equation ht
  dsimp only [envelope]
  generalize hz : envelopeRoot t = z at h ⊢
  rw [← h]
  ring

theorem envelope_le_iff {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) :
    envelope t ≤ R ↔ t ^ 3 ≤ R ^ 2 + (3 * t + 1) * R := by
  have hf := envelope_nonneg ht
  have heq := envelope_equation ht
  constructor
  · intro h
    nlinarith [mul_nonneg (show 0 ≤ R - envelope t by linarith)
      (show 0 ≤ R + envelope t + 3 * t + 1 by linarith)]
  · intro h
    by_contra h'
    have hp : 0 < (envelope t - R) * (envelope t + R + 3 * t + 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem envelope_lt_iff {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) :
    envelope t < R ↔ t ^ 3 < R ^ 2 + (3 * t + 1) * R := by
  have hf := envelope_nonneg ht
  have heq := envelope_equation ht
  constructor
  · intro h
    have hp : 0 < (R - envelope t) * (R + envelope t + 3 * t + 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · intro h
    by_contra h'
    nlinarith [mul_nonneg (show 0 ≤ envelope t - R by linarith)
      (show 0 ≤ envelope t + R + 3 * t + 1 by linarith)]

theorem envelope_two_mul_le {n : ℝ} (hn : 0 ≤ n) : envelope (2 * n) ≤ n ^ 2 := by
  apply (envelope_le_iff (by positivity) (sq_nonneg n)).2
  nlinarith [mul_nonneg (sq_nonneg n) (sq_nonneg (n - 1))]

theorem envelope_square_lt {n : ℝ} (hn : 2 ≤ n) : envelope (n ^ 2) < n ^ 3 - n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hR : 0 ≤ n ^ 3 - n ^ 2 := by nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ n - 1 by linarith)]
  apply (envelope_lt_iff (sq_nonneg n) hR).2
  have hs : 1 ≤ (n - 1) ^ 2 := by nlinarith [sq_nonneg (n - 2)]
  have hm := mul_le_mul_of_nonneg_left hs hn0.le
  have hp : 0 < n ^ 2 * (n * (n - 1) ^ 2 - 1) :=
    mul_pos (sq_pos_of_pos hn0) (by nlinarith)
  nlinarith

theorem envelope_lt_mul {n t : ℝ} (hn : 0 < n) (ht : 0 < t) (htn : t ≤ n ^ 2 + 3 * n) :
    envelope t < n * t := by
  apply (envelope_lt_iff ht.le (mul_pos hn ht).le).2
  have hp : 0 < t * (t * (n ^ 2 + 3 * n - t) + n) :=
    mul_pos ht (add_pos_of_nonneg_of_pos (mul_nonneg ht.le (by linarith)) hn)
  nlinarith

def supportCost (r : ℝ) : ℝ := r ^ (2 / 3 : ℝ) + r ^ (1 / 3 : ℝ)

theorem supportCost_concave : ConcaveOn ℝ (Set.Ici 0) supportCost :=
  (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)).add
    (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num))

theorem supportCost_strictMono {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    supportCost x < supportCost y := by
  have h₁ := Real.rpow_le_rpow hx hxy.le (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have h₂ := Real.rpow_lt_rpow hx hxy (by norm_num : (0 : ℝ) < 1 / 3)
  exact add_lt_add_of_le_of_lt h₁ h₂

theorem supportCost_envelope {t : ℝ} (ht : 0 ≤ t) : supportCost (envelope t) = t := by
  have hz := envelopeRoot_nonneg ht
  have h₁ : envelope t ^ (1 / 3 : ℝ) = envelopeRoot t := by
    rw [envelope, ← Real.rpow_natCast, ← Real.rpow_mul hz]
    norm_num
  have h₂ : envelope t ^ (2 / 3 : ℝ) = envelopeRoot t ^ 2 := by
    rw [envelope, ← Real.rpow_natCast, ← Real.rpow_mul hz]
    norm_num
  rw [supportCost, h₁, h₂]
  exact envelopeRoot_equation ht

theorem envelope_convex : ConvexOn ℝ (Set.Ici 0) envelope := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfx := envelope_nonneg hx
  have hfy := envelope_nonneg hy
  have hR : 0 ≤ a * envelope x + b * envelope y :=
    add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hfy)
  have hw : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hc := supportCost_concave.2 hfx hfy ha hb hab
  simp only [smul_eq_mul, supportCost_envelope hx, supportCost_envelope hy] at hc ⊢
  by_contra h
  have hlt : a * envelope x + b * envelope y < envelope (a * x + b * y) := by linarith
  have hcost := supportCost_strictMono hR hlt
  rw [supportCost_envelope hw] at hcost
  linarith

theorem envelope_mono : MonotoneOn envelope (Set.Ici 0) := by
  intro x hx y hy hxy
  by_contra h
  have hlt : envelope y < envelope x := by linarith
  have hc := supportCost_strictMono (envelope_nonneg hy) hlt
  rw [supportCost_envelope hx, supportCost_envelope hy] at hc
  linarith

@[simp] theorem supportCost_one : supportCost 1 = 2 := by norm_num [supportCost]

theorem supportCost_hasDerivAt_one : HasDerivAt supportCost 1 1 := by
  have h₁ := Real.hasDerivAt_rpow_const (x := 1) (p := (2 / 3 : ℝ)) (Or.inl one_ne_zero)
  have h₂ := Real.hasDerivAt_rpow_const (x := 1) (p := (1 / 3 : ℝ)) (Or.inl one_ne_zero)
  convert h₁.add h₂ using 1 <;> norm_num [supportCost]
  funext x
  rfl

theorem supportCost_tangent_one {r : ℝ} (hr : 1 ≤ r) : supportCost r ≤ r + 1 := by
  obtain hr | hr := eq_or_lt_of_le hr
  · subst r
    norm_num
  · have h := supportCost_concave.slope_le_of_hasDerivAt (by norm_num : (1 : ℝ) ∈ Set.Ici 0)
      (by change 0 ≤ r; linarith) hr supportCost_hasDerivAt_one
    rw [slope_def_field, supportCost_one] at h
    have h' := (div_le_iff₀ (show 0 < r - 1 by linarith)).mp h
    linarith

def dimensionCost (d : ℕ) : ℝ := if d ≤ 1 then d else supportCost ((d : ℝ) - 1)

@[simp] theorem dimensionCost_zero : dimensionCost 0 = 0 := by simp [dimensionCost]
@[simp] theorem dimensionCost_one : dimensionCost 1 = 1 := by simp [dimensionCost]
@[simp] theorem dimensionCost_two : dimensionCost 2 = 2 := by norm_num [dimensionCost]

theorem dimensionCost_concave (n : ℕ) :
    dimensionCost (n + 2) + dimensionCost n ≤ 2 * dimensionCost (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  by_cases hn1 : n = 1
  · subst n
    have h := supportCost_tangent_one (by norm_num : (1 : ℝ) ≤ 2)
    norm_num [dimensionCost] at h ⊢
    linarith
  have hn : 2 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := supportCost_concave.2
    (show (n : ℝ) - 1 ∈ Set.Ici 0 by change 0 ≤ (n : ℝ) - 1; linarith)
    (show (n : ℝ) + 1 ∈ Set.Ici 0 by change 0 ≤ (n : ℝ) + 1; linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) * ((n : ℝ) - 1) + (1 / 2 : ℝ) * ((n : ℝ) + 1) = n := by ring
  simp only [smul_eq_mul, hmid] at hc
  simp only [dimensionCost, show ¬ n + 2 ≤ 1 by omega, show ¬ n + 1 ≤ 1 by omega,
    show ¬ n ≤ 1 by omega, ite_false, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have heq₁ : (n : ℝ) + 2 - 1 = n + 1 := by ring
  have heq₂ : (n : ℝ) + 1 - 1 = n := by ring
  rw [heq₁, heq₂]
  linarith

theorem dimensionCost_increment_anti :
    Antitone (fun n => dimensionCost (n + 1) - dimensionCost n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := dimensionCost_concave n
  linarith

theorem dimensionCost_add (a b : ℕ) : dimensionCost (a + b) ≤ dimensionCost a + dimensionCost b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h := dimensionCost_increment_anti (show b ≤ a + b by omega)
    have heq : a + (b + 1) = a + b + 1 := by omega
    rw [heq]
    linarith

theorem dimensionCost_sum {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    dimensionCost (∑ i ∈ s, d i) ≤ ∑ i ∈ s, dimensionCost (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (dimensionCost_add _ _).trans (add_le_add (le_refl _) ih)

theorem dimension_le_envelope {d : ℕ} {m : ℝ} (hm : 0 ≤ m) (hd : dimensionCost d ≤ m) :
    (d : ℝ) ≤ 1 + envelope m := by
  by_cases hd1 : d ≤ 1
  · have hdR : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
    have hf := envelope_nonneg hm
    linarith
  · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    simp only [dimensionCost, hd1, ite_false] at hd
    by_contra h
    have hlt : envelope m < (d : ℝ) - 1 := by linarith
    have hc := supportCost_strictMono (envelope_nonneg hm) hlt
    rw [supportCost_envelope hm] at hc
    linarith

theorem envelope_pair_bound {l C x y : ℝ} (hl : 0 ≤ l) (hx : l ≤ x) (hy : l ≤ y)
    (hxy : x + y ≤ C) : envelope x + envelope y ≤ envelope l + envelope (C - l) := by
  have hlC : l ≤ C - l := by linarith
  let ψ : ℝ → ℝ := fun z => envelope z + envelope (C - z)
  have hψ : ConvexOn ℝ (Set.Icc l (C - l)) ψ := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro u hu v hv a b ha hb hab
    have hu0 : 0 ≤ u := hl.trans hu.1
    have hv0 : 0 ≤ v := hl.trans hv.1
    have hCu : 0 ≤ C - u := by linarith [hu.2]
    have hCv : 0 ≤ C - v := by linarith [hv.2]
    have hc₁ := envelope_convex.2 hu0 hv0 ha hb hab
    have hc₂ := envelope_convex.2 hCu hCv ha hb hab
    have hcomb : C - (a * u + b * v) = a * (C - u) + b * (C - v) := by
      nlinarith [congrArg (fun z : ℝ => z * C) hab]
    simp only [ψ, smul_eq_mul, hcomb] at hc₁ hc₂ ⊢
    nlinarith
  have hp := hψ.le_max_of_mem_Icc ⟨le_rfl, hlC⟩ ⟨hlC, le_rfl⟩
    (show x ∈ Set.Icc l (C - l) by constructor; exact hx; linarith)
  have hCC : C - (C - l) = l := by ring
  have hp' : envelope x + envelope (C - x) ≤ envelope l + envelope (C - l) := by
    simpa only [ψ, hCC, add_comm (envelope (C - l)) (envelope l), max_self] using hp
  have hm := envelope_mono (show y ∈ Set.Ici 0 from hl.trans hy)
    (show C - x ∈ Set.Ici 0 by change 0 ≤ C - x; linarith) (show y ≤ C - x by linarith)
  exact (add_le_add (le_refl _) hm).trans hp'

end Lemmata.Centroid.General
