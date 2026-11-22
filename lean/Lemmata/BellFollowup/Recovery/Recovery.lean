module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A finite-dimensional recovery criterion from a coordinate gap and pair decay

The vectors are in normalized real harmonic coordinates. This module proves the
finite-dimensional implication used by the fixed-settings Bell argument. The
Fourier estimates supplying its hypotheses are separate mathematics.
-/

namespace Lemmata.BellFollowup.Recovery

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Coordinate ℓ¹ norm, independent of the default norm on a function space. -/
noncomputable def mass (x : ι → ℝ) : ℝ := ∑ i, |x i|

private theorem one_exception (x : ι → ℝ) (k : ι) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i, i ≠ k → |x i| ≤ b) :
    mass x ≤ |x k| + (Fintype.card ι : ℝ) * b := by
  classical
  calc
    mass x ≤ ∑ i, ((if k = i then |x k| else 0) + b) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : k = i
      · subst i
        simp [hb]
      · simpa [hi] using h i (Ne.symm hi)
    _ = _ := by simp [Finset.sum_add_distrib]

omit [Fintype ι] in
private theorem tail_le {x : ι → ℝ} {k : ι} {t b : ℝ} (hb : 0 < b)
    (hk : b ≤ |x k|) (hpair : ∀ i j, i ≠ j → |x i| * |x j| ≤ t) :
    ∀ i, i ≠ k → |x i| ≤ t / b := by
  intro i hi
  apply (le_div_iff₀ hb).2
  exact (mul_le_mul_of_nonneg_left hk (abs_nonneg _)).trans (hpair i k hi)

/-- A uniform gap and two-coordinate decay put the ℓ¹ mass strictly below
the smallest admissible distortion of a near-identity matrix. -/
theorem mass_add_margin_lt_one (x : ι → ℝ) {m t : ℝ} (hm : 2 ≤ m)
    (hd : (Fintype.card ι : ℝ) ≤ m) (ht : 0 ≤ t)
    (hcut : t ≤ 1 / (4 * m ^ 3))
    (hgap : ∀ i, |x i| ≤ 1 - 1 / m ^ 2)
    (hpair : ∀ i j, i ≠ j → |x i| * |x j| ≤ t) :
    mass x + m * t < 1 := by
  classical
  have hm0 : 0 < m := by linarith
  have hm4 : (4 : ℝ) ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 2)]
  have hmt : m * t ≤ 1 / (4 * m ^ 2) := calc
    m * t ≤ m * (1 / (4 * m ^ 3)) := mul_le_mul_of_nonneg_left hcut hm0.le
    _ = _ := by field_simp
  have hmtSmall : m * t ≤ 1 / 16 := by
    apply hmt.trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * m ^ 2)).2
    linarith
  have hmmt : m * (m * t) ≤ 1 / (4 * m) := calc
    m * (m * t) ≤ m * (1 / (4 * m ^ 2)) := mul_le_mul_of_nonneg_left hmt hm0.le
    _ = _ := by field_simp
  have hmmtSmall : m * (m * t) ≤ 1 / 8 := by
    apply hmmt.trans
    apply (div_le_iff₀ (by positivity : 0 < 4 * m)).2
    linarith
  by_cases hbig : ∃ k, (1 / 2 : ℝ) ≤ |x k|
  · obtain ⟨k, hk⟩ := hbig
    have ht' : 0 ≤ t / (1/2 : ℝ) := by positivity
    have hs := one_exception x k ht' (tail_le (by norm_num : (0:ℝ)<1/2) hk hpair)
    have hd' := mul_le_mul_of_nonneg_right hd ht'
    have hstrict : 3 * (1 / (4 * m ^ 2)) < 1 / m ^ 2 := by
      have hpos : 0 < 1 / m ^ 2 := by positivity
      have heq : 3 * (1 / (4 * m ^ 2)) = (3/4) * (1 / m ^ 2) := by field_simp
      rw [heq]
      linarith
    norm_num at hs hd'
    linarith [hgap k]
  · by_cases hmid : ∃ k, 1 / (2 * m) ≤ |x k|
    · obtain ⟨k, hk⟩ := hmid
      have hb : 0 < 1 / (2 * m) := by positivity
      have ht' : 0 ≤ t / (1 / (2 * m)) := by positivity
      have hs := one_exception x k ht' (tail_le hb hk hpair)
      have hd' := mul_le_mul_of_nonneg_right hd ht'
      have hk' : |x k| < 1 / 2 := lt_of_not_ge (fun hk' => hbig ⟨k, hk'⟩)
      have heq : m * (t / (1 / (2 * m))) = 2 * (m * (m * t)) := by
        rw [one_div, div_inv_eq_mul]; ring
      linarith
    · have hs : mass x ≤ (Fintype.card ι : ℝ) * (1 / (2 * m)) := calc
        mass x ≤ ∑ _i : ι, (1 / (2 * m)) := by
          apply Finset.sum_le_sum
          intro i _
          exact (lt_of_not_ge (fun hi => hmid ⟨i, hi⟩)).le
        _ = _ := by simp
      have hd' := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 1 / (2 * m))
      have heq : m * (1 / (2 * m)) = 1 / 2 := by field_simp
      linarith


theorem mass_nonneg (x : ι → ℝ) : 0 ≤ mass x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private theorem error_row {E : ι → ι → ℝ} {t : ℝ}
    (he : ∀ i j, |E i j| ≤ t) (z : ι → ℝ) (i : ι) :
    |∑ j, E i j * z j| ≤ t * mass z := by
  calc
    |∑ j, E i j * z j| ≤ ∑ j, |E i j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, t * |z j| := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _)
    _ = _ := by rw [mass, Finset.mul_sum]

/-- The coordinate identity expresses the given linear map as identity plus a
matrix error. It does not presuppose that the map is invertible. -/
theorem mass_lower_bound (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (E : ι → ι → ℝ) {m t : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ m) (ht : 0 ≤ t)
    (he : ∀ i j, |E i j| ≤ t)
    (hL : ∀ z i, L z i = z i + ∑ j, E i j * z j)
    (z : ι → ℝ) : (1 - m * t) * mass z ≤ mass (L z) := by
  have hz (i : ι) : |z i| ≤ |L z i| + t * mass z := calc
    |z i| = |L z i + -(∑ j, E i j * z j)| := by rw [hL]; simp
    _ ≤ |L z i| + |-(∑ j, E i j * z j)| := abs_add_le _ _
    _ ≤ |L z i| + t * mass z := by
      rw [abs_neg]
      linarith [error_row he z i]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => hz i)
  have hsum' : mass z ≤ mass (L z) + (Fintype.card ι : ℝ) * (t * mass z) := by
    simpa [mass, Finset.sum_add_distrib] using hsum
  have hcard := mul_le_mul_of_nonneg_right hd (mul_nonneg ht (mass_nonneg z))
  linarith

/-- A positive lower bound in coordinate mass forces injectivity. -/
theorem injective_of_mass_lower_bound
    (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {c : ℝ} (hc : 0 < c)
    (h : ∀ z, c * mass z ≤ mass (L z)) : Function.Injective L := by
  classical
  intro a b hab
  have hzero : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h' := h (a - b)
  rw [hzero] at h'
  have hmasszero : mass (0 : ι → ℝ) = 0 := by simp [mass]
  rw [hmasszero] at h'
  have hmass : mass (a - b) ≤ 0 := by
    by_contra! hpos
    exact (not_lt_of_ge h') (mul_pos hc hpos)
  funext i
  have hi : |(a - b) i| ≤ mass (a - b) :=
    Finset.single_le_sum (f := fun j => |(a - b) j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hi' : |(a - b) i| = 0 := le_antisymm (hi.trans hmass) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hi')

/-- A point with strict ℓ¹ margin has a unique inverse under the near-identity
map, and that inverse lies in the open ℓ¹ unit ball. -/
theorem exists_unique_preimage_of_margin
    (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (E : ι → ι → ℝ) {m t : ℝ}
    (hd : (Fintype.card ι : ℝ) ≤ m) (ht : 0 ≤ t)
    (he : ∀ i j, |E i j| ≤ t)
    (hL : ∀ z i, L z i = z i + ∑ j, E i j * z j)
    (x : ι → ℝ) (hx : mass x + m * t < 1) :
    ∃! z : ι → ℝ, L z = x ∧ mass z < 1 := by
  have hc : 0 < 1 - m * t := by linarith [mass_nonneg x]
  have hlower := mass_lower_bound L E hd ht he hL
  have hinj := injective_of_mass_lower_bound L hc hlower
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨z, hz⟩ := hsurj x
  have hmz := hlower z
  rw [hz] at hmz
  have hlt : mass z < 1 := by
    by_contra! hn
    have hc' := mul_le_mul_of_nonneg_left hn hc.le
    linarith
  exact ⟨z, ⟨hz, hlt⟩, fun y hy => hinj (hy.1.trans hz.symm)⟩

/-- Generic recovery with the same uniform cutoff as the Bell proof. Substitute
twice (5/8)^N for the pair bound, or just (5/8)^N for odd settings. -/
theorem recovery_of_pair_decay
    (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (E : ι → ι → ℝ) {m t : ℝ}
    (hm : 2 ≤ m) (hd : (Fintype.card ι : ℝ) ≤ m) (ht : 0 ≤ t)
    (hcut : t ≤ 1 / (4 * m ^ 3))
    (he : ∀ i j, |E i j| ≤ t)
    (hL : ∀ z i, L z i = z i + ∑ j, E i j * z j)
    (x : ι → ℝ) (hgap : ∀ i, |x i| ≤ 1 - 1 / m ^ 2)
    (hpair : ∀ i j, i ≠ j → |x i| * |x j| ≤ t) :
    ∃! z : ι → ℝ, L z = x ∧ mass z < 1 :=
  exists_unique_preimage_of_margin L E hd ht he hL x
    (mass_add_margin_lt_one x hm hd ht hcut hgap hpair)

/-- Arithmetic specialization of the cutoff in the all-settings theorem. -/
theorem all_settings_cutoff {m : ℝ} {N : ℕ} (hm : 2 ≤ m)
    (h : (5 / 8 : ℝ) ^ N ≤ 1 / (8 * m ^ 3)) :
    2 * (5 / 8 : ℝ) ^ N ≤ 1 / (4 * m ^ 3) := by
  calc
    _ ≤ 2 * (1 / (8 * m ^ 3)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by
      have : 0 < m := by linarith
      field_simp; ring

end Lemmata.BellFollowup.Recovery
