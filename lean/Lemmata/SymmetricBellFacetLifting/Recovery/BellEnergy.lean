module

public import Lemmata.SymmetricBellFacetLifting.Recovery.BellFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The actual normalization at harmonic 2k+1 uses gcd(2k+1,m) parallel
copies of each generator direction. This module proves an unconditional
energy estimate for all odd modes of a deterministic row. -/

@[expose] public section

namespace Lemmata.SymmetricBellFacetLifting.Recovery.BellFourier

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- The reciprocal of the polygon circumradius at odd mode 2k+1. -/
noncomputable def inverseRadius (k : ZMod m) : ℝ :=
  let g : ℝ := (2 * k.val + 1).gcd m
  Real.sin (Real.pi * g / (2 * m)) / g

theorem inverseRadius_bounds (k : ZMod m) :
    0 ≤ inverseRadius k ∧ inverseRadius k ≤ Real.pi / (2 * m) := by
  let g : ℕ := (2*k.val+1).gcd m
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hg : 0 < (g : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_right _ (NeZero.pos m)
  have hgm : (g : ℝ) ≤ m := by exact_mod_cast Nat.gcd_le_right _ (NeZero.pos m)
  let θ := Real.pi * g / (2 * m)
  have ht : 0 ≤ θ := by dsimp [θ]; positivity
  have ht' : θ ≤ Real.pi := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (m : ℝ))).2
    nlinarith [mul_le_mul_of_nonneg_left hgm Real.pi_nonneg, mul_nonneg Real.pi_nonneg hm.le]
  change 0 ≤ Real.sin θ / g ∧ Real.sin θ / g ≤ _
  refine ⟨div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht ht') hg.le, ?_⟩
  calc
    Real.sin θ / g ≤ θ / g := div_le_div_of_nonneg_right (Real.sin_le ht) hg.le
    _ = _ := by dsimp [θ]; field_simp

/-- Magnitude of the odd-harmonic evaluation divided by its polygon radius. -/
noncomputable def normalized (s : ZMod m → Bool) (k : ZMod m) : ℝ :=
  inverseRadius k * ‖amplitude (signs s) k‖

theorem normalized_nonneg (s : ZMod m → Bool) (k : ZMod m) : 0 ≤ normalized s k :=
  mul_nonneg (inverseRadius_bounds k).1 (norm_nonneg _)

/-- Exact unnormalized Parseval and the sine estimate imply a uniform
normalized energy bound over the full spectrum, counting each conjugate. -/
theorem full_energy (s : ZMod m → Bool) :
    (∑ k, normalized s k ^ 2) ≤ Real.pi ^ 2 / 4 := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  calc
    (∑ k, normalized s k ^ 2) ≤ ∑ k, (Real.pi / (2*m) * ‖amplitude (signs s) k‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (normalized_nonneg s k)
      exact mul_le_mul_of_nonneg_right (inverseRadius_bounds k).2 (norm_nonneg _)
    _ = (Real.pi / (2*m))^2 * (∑ k, ‖amplitude (signs s) k‖ ^ 2) := by
      simp only [mul_pow, Finset.mul_sum]
    _ = Real.pi ^ 2 / 4 := by rw [signs_parseval]; field_simp; ring

theorem pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have hx := mul_pos (sub_pos.mpr Real.pi_lt_d2) (show 0 < 3.15 + Real.pi by positivity)
  nlinarith

theorem full_energy_lt (s : ZMod m → Bool) :
    (∑ k, normalized s k ^ 2) < (5 : ℝ)/2 := by
  linarith [full_energy s, pi_sq_lt_ten]

/-- Canonical representative of each conjugate pair, including a real fixed
mode when one exists. Comparison is of the standard setting representatives. -/
def kept (k : ZMod m) : Prop := k.val ≤ (reflect k).val

instance (k : ZMod m) : Decidable (kept k) := inferInstanceAs (Decidable (_ ≤ _))

private theorem inverseRadius_of_fixed {k : ZMod m} (hk : reflect k = k) :
    inverseRadius k = 1 / (m : ℝ) := by
  have hzero : ((2 * k.val + 1 : ℕ) : ZMod m) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    unfold reflect at hk
    linear_combination -hk
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hq : 2*k.val+1 = m :=
    Nat.eq_of_dvd_of_lt_two_mul (by omega) hdiv (by have := k.val_lt; omega)
  unfold inverseRadius
  rw [hq, Nat.gcd_self]
  have heq : Real.pi * m / (2 * m) = Real.pi/2 := by field_simp
  change Real.sin (Real.pi * m / (2 * m)) / m = 1 / m
  rw [heq, Real.sin_pi_div_two]

private theorem normalized_sq_bound (s : ZMod m → Bool) (k : ZMod m) :
    normalized s k ^ 2 ≤ (5 / (2*(m:ℝ)^2)) * ‖amplitude (signs s) k‖^2 := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hsc := pow_le_pow_left₀ (inverseRadius_bounds k).1 (inverseRadius_bounds k).2 2
  have hπ : (Real.pi/(2*m))^2 ≤ 5 / (2*(m:ℝ)^2) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr pi_sq_lt_ten.le) (sq_nonneg (m:ℝ))]
  unfold normalized
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (hsc.trans hπ) (sq_nonneg _)

/-- The independent real harmonics of every deterministic Bell row have
normalized total squared energy at most 5/4, uniformly in m. -/
theorem independent_energy (s : ZMod m → Bool) :
    (∑ k ∈ Finset.univ.filter kept, normalized s k ^ 2) ≤ (5:ℝ)/4 := by
  classical
  let F : ZMod m → ℝ := fun k => if kept k then normalized s k ^ 2 else 0
  have hk (k : ZMod m) :
      F k + F (reflect k) ≤ (5 / (2*(m:ℝ)^2)) * ‖amplitude (signs s) k‖^2 := by
    by_cases he : reflect k = k
    · have hkeep : kept k := by simp [kept, he]
      simp only [F, he, hkeep, ↓reduceIte, normalized, inverseRadius_of_fixed he]
      have hsq := sq_nonneg ‖amplitude (signs s) k‖
      have hm : 0 < (m:ℝ) := by exact_mod_cast NeZero.pos m
      field_simp
      nlinarith
    · by_cases hkeep : kept k
      · have hnot : ¬ kept (reflect k) := by
          intro hr
          have H : (reflect k).val = k.val := by
            apply le_antisymm _ hkeep
            simpa [kept] using hr
          exact he (ZMod.val_injective m H)
        simpa [F, hkeep, hnot] using normalized_sq_bound s k
      · have hr : kept (reflect k) := by
          simp only [kept, reflect_reflect]
          exact (lt_of_not_ge hkeep).le
        simpa [F, hkeep, hr, amplitude_reflect_norm] using normalized_sq_bound s (reflect k)
  let e : ZMod m ≃ ZMod m :=
    ⟨reflect, reflect, reflect_reflect, reflect_reflect⟩
  have hsum : ∑ k, F (reflect k) = ∑ k, F k :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hd := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod m))) (fun k _ => hk k)
  rw [Finset.sum_add_distrib, hsum, ← Finset.mul_sum, signs_parseval] at hd
  have hm : 0 < (m:ℝ) := by exact_mod_cast NeZero.pos m
  have hconst : (5 / (2 * (m:ℝ)^2)) * (m:ℝ)^2 = 5/2 := by field_simp
  rw [hconst] at hd
  have h := Finset.sum_filter (s := (Finset.univ : Finset (ZMod m))) (p := kept)
    (f := fun k => normalized s k ^ 2)
  change (∑ k ∈ Finset.univ.filter kept, normalized s k ^ 2) ≤ _
  rw [h]
  change (∑ k, F k) ≤ _
  linarith

end Lemmata.SymmetricBellFacetLifting.Recovery.BellFourier
