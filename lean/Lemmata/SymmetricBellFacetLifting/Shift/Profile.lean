module

public import Lemmata.SymmetricBellFacetLifting.Shift.Analytic
public import Lemmata.SymmetricBellFacetLifting.Shift.Secondary

/-! # Uniform separation from reindexed large-order frequency profiles -/

@[expose] public section

namespace Lemmata.SymmetricBellFacetLifting.Shift

noncomputable section

/-- Score of a reindexed reduced-frequency profile. The map `idx` assigns the
physical index to each odd harmonic order. The function `phase` allows arbitrary
phases at all orders, including those of the pure frequency strategies. -/
def profileScore (x p g : ℝ) (n : ℕ) (idx : ℝ → ℕ) (phase : ℝ → ℝ) : ℝ :=
  let a j := testCoefficient x p (idx j) * Real.cos (phase j)
  polygonScale x g * (a 1 + oddSum (fun j => a j * secondaryCube (g*x) j) n 3)

/-- Only the fundamental and the eleven selected harmonics can be active. -/
theorem coefficient_vanishes_above (x p : ℝ) {k : ℕ} (hk : 23 < k) :
    testCoefficient x p k = 0 := by
  have hs : harmonics ⊆ Finset.Icc 1 23 := by decide
  have hn : k ∉ harmonics := by
    intro h
    have hm := (Finset.mem_Icc.mp (hs h)).2
    omega
  simp [testCoefficient, hn, (show k ≠ 1 by omega)]

/-- On the physical support multiples `g*j` of a short reduced polygon, the
nonzero test coefficients are confined to `g` for length below 12 and to
`g, 3g` for length below 16. The claim also applies to active coefficients
arising at secondary orders under reindexing. -/
theorem short_active_indices (x p : ℝ) (g L j : ℕ) (hg : 0 < g) (hm : 92 ≤ g*L)
    (hj : Odd j) (ha : testCoefficient x p (g*j) ≠ 0) :
    (L < 12 → j = 1) ∧ (L < 16 → j = 1 ∨ j = 3) := by
  have hk : g*j ≤ 23 := by
    by_contra! h
    exact ha (coefficient_vanishes_above x p h)
  have hcut : 4*j ≤ L := by
    apply Nat.le_of_mul_le_mul_left (c := g) _ hg
    calc
      _ = 4*(g*j) := by ring
      _ ≤ g*L := by omega
  obtain ⟨k, hk⟩ := hj
  omega

private theorem abs_cos_cap (a t c : ℝ) (h : |a| ≤ c) : |a * Real.cos t| ≤ c := by
  rw [abs_mul]
  have hcos : |Real.cos t| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc
    _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ ≤ c := by simpa using h

/-- Every reindexing whose primary index differs from one, even with arbitrary
phases at all orders, satisfies the reference bound for gcd-reduced lengths at
least sixteen. This unrestricted `idx` bound includes all injective reindexings. -/
theorem profile_score_bound {x p g : ℝ} (hx : 0 < x) (hm : x ≤ 171/10000)
    (hp : 0 ≤ p) (hpx : p ≤ x) (hg : 1 ≤ g) (hy : g*x ≤ Real.pi/32)
    (n : ℕ) (ht : (2*(n : ℝ)+1)*(g*x) ≤ Real.pi/2)
    (idx : ℝ → ℕ) (hi : idx 1 ≠ 1) (phase : ℝ → ℝ) :
    |profileScore x p g n idx phase| < 1 := by
  unfold profileScore
  exact many_mode_bound x g hx hg hy n ht
    (fun j => testCoefficient x p (idx j) * Real.cos (phase j))
    (abs_cos_cap _ _ _ (coefficient_nonfund x p hi))
    (fun k _ => abs_cos_cap _ _ _ (coefficient_bound hx hm hp hpx (idx (3+2*k))))

/-- Both parity choices of the reference phase are separated by one setting shift
from every nonfundamental reindexed large-order frequency profile. -/
theorem shift_separates_profiles (m : ℕ) (hm : 92 ≤ m) (p g : ℝ) (n : ℕ)
    (idx : ℝ → ℕ) (phase : ℝ → ℝ) :
    let x := Real.pi/(2*(m : ℝ))
    (p = 0 ∨ p = x) → 1 ≤ g → g*x ≤ Real.pi/32 →
      (2*(n : ℝ)+1)*(g*x) ≤ Real.pi/2 → idx 1 ≠ 1 →
      score x p p = 1 ∧ |profileScore x p g n idx phase| < 1 ∧
        1 < score x p (p+2*x) := by
  set x := Real.pi/(2*(m : ℝ))
  dsimp only
  intro hp hg hy ht hi
  have hm' : (92 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < 2*(m : ℝ) := by linarith
  have hx : 0 < x := div_pos Real.pi_pos hden
  have hx' : x ≤ 171/10000 := by
    apply (div_le_iff₀ hden).2
    linarith [Real.pi_lt_d4]
  have res := shifted_score x hx hx'
  rcases hp with h | h
  · subst p
    exact ⟨res.1.1, profile_score_bound hx hx' (by norm_num) hx.le hg hy n ht idx hi phase,
      by simpa using res.1.2⟩
  · subst p
    exact ⟨res.2.1, profile_score_bound hx hx' hx.le le_rfl hg hy n ht idx hi phase,
      by simpa only [show x+2*x=3*x by ring] using res.2.2⟩

end
end Lemmata.SymmetricBellFacetLifting.Shift
