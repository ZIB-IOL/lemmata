module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Finite signed-coordinate estimates for the Hilbert-space companion. The geometric
oracle argument supplies the one-step hypothesis of `hull_after_queries`. -/
@[expose] public section

namespace Lemmata.FrankWolfePS.Hilbert

open scoped BigOperators

/-- Beyond the prefix, every off-diagonal Gram entry uses the new index. -/
theorem tail_sum (s : Finset ℕ) (j : ℕ) (w ξ : ℕ → ℝ)
    (h : ∀ i ∈ s, i ≤ j) :
    (∑ i ∈ s, ξ i * w (max i j)) = (∑ i ∈ s, ξ i) * w j := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i hi => by rw [max_eq_right (h i hi)])

/-- Extremal tail derivatives are separated, independently of the allocation. -/
theorem next_strict (m w u k : ℝ) (hm : 0 < m) (hw : 0 < w)
    (hu : u ≤ w / 2) (hk : k * w < m / 2) :
    m * u < m * w - k * w ^ 2 := by
  have h₁ := mul_le_mul_of_nonneg_left hu (le_of_lt hm)
  have h₂ := mul_lt_mul_of_pos_right hk hw
  nlinarith

/-- The mass of the returned atom stays inside the induction interval. -/
theorem reply_mass (m d : ℝ) (hm₀ : (1 : ℝ) / 2 ≤ m) (hm₁ : m ≤ 5 / 4)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 2 / 5) :
    (1 : ℝ) / 2 ≤ 1 - d * m ∧ 1 - d * m ≤ 5 / 4 := by
  have hm : 0 ≤ m := by linarith
  have h₀ := mul_nonneg hd₀ hm
  have h₁ := mul_le_mul_of_nonneg_right hd₁ hm
  constructor <;> linarith

/-- The final scalar estimate given the Gram, mass and support inequalities. -/
theorem support_gap (n h en m : ℝ) (hn : 0 < n)
    (hm : (1 : ℝ) / 2 ≤ m) (hcs : m ^ 2 ≤ n * en) (hg : (31 : ℝ) / 64 * en ≤ h) :
    (31 : ℝ) / (256 * n) ≤ h := by
  apply (div_le_iff₀ (by positivity : 0 < 256 * n)).2
  have h₁ := mul_le_mul_of_nonneg_left hg (le_of_lt hn)
  nlinarith [sq_nonneg (m - 1 / 2)]

/-- A signed sequence supported on the first `n` coordinates, with controlled total mass. -/
def prefixSlice (n : ℕ) : Set (ℕ → ℝ) :=
  {x | (∀ j, n ≤ j → x j = 0) ∧
    1 / 2 ≤ ∑ j ∈ Finset.range n, x j ∧ (∑ j ∈ Finset.range n, x j) ≤ 5 / 4}

theorem convex_prefixSlice (n : ℕ) : Convex ℝ (prefixSlice n) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx₀, hxl, hxu⟩
  rcases hy with ⟨hy₀, hyl, hyu⟩
  have hcomb : (∑ j ∈ Finset.range n, (a • x + b • y) j) =
      a * (∑ j ∈ Finset.range n, x j) + b * (∑ j ∈ Finset.range n, y j) := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
  constructor
  · intro j hj
    simp [Pi.add_apply, Pi.smul_apply, hx₀ j hj, hy₀ j hj]
  · rw [hcomb]
    constructor
    · linarith [mul_le_mul_of_nonneg_left hxl ha, mul_le_mul_of_nonneg_left hyl hb]
    · linarith [mul_le_mul_of_nonneg_left hxu ha, mul_le_mul_of_nonneg_left hyu hb]

theorem prefix_mono (n : ℕ) : prefixSlice n ⊆ prefixSlice (n + 1) := by
  rintro x ⟨hx, hl, hu⟩
  constructor
  · intro j hj
    exact hx j (Nat.le_trans (Nat.le_succ n) hj)
  · rw [Finset.sum_range_succ, hx n (le_refl n), add_zero]
    exact ⟨hl, hu⟩

/-- If each gradient query on the current hull produces an atom in the next prefix slice,
every feasible hull output after `t` replies belongs to the first `t + 1` coordinates. -/
theorem hull_after_queries (seed : ℕ → ℝ) (query reply : ℕ → ℕ → ℝ)
    (hseed : seed ∈ prefixSlice 1)
    (hq : ∀ t, query t ∈ convexHull ℝ (insert seed (reply '' Set.Iio t)))
    (hs : ∀ t, query t ∈ prefixSlice (t + 1) → reply t ∈ prefixSlice (t + 2)) :
    ∀ t, convexHull ℝ (insert seed (reply '' Set.Iio t)) ⊆ prefixSlice (t + 1) := by
  intro t
  induction t with
  | zero =>
    apply convexHull_min _ (convex_prefixSlice _)
    intro x hx
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · exact hseed
    · exact False.elim (Nat.not_lt_zero k hk)
  | succ t ih =>
    apply convexHull_min _ (convex_prefixSlice _)
    have old : insert seed (reply '' Set.Iio t) ⊆ prefixSlice (t + 1) :=
      (subset_convexHull ℝ _).trans ih
    intro x hx
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · exact prefix_mono _ (old (Set.mem_insert _ _))
    · change k < t + 1 at hk
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
      · exact prefix_mono _ (old (Set.mem_insert_of_mem _ ⟨k, hlt, rfl⟩))
      · subst k
        exact hs t (ih (hq t))

/-- Finite Cauchy–Schwarz gives the stated lower bound for signed coordinates in the slice. -/
theorem prefix_gap (t : ℕ) (x : ℕ → ℝ) (h : ℝ) (hx : x ∈ prefixSlice (t + 1))
    (he : (31 : ℝ) / 64 * (∑ j ∈ Finset.range (t + 1), x j ^ 2) ≤ h) :
    (31 : ℝ) / (256 * ((t : ℝ) + 1)) ≤ h := by
  apply support_gap _ _ _ _ (by positivity) hx.2.1 _ he
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (t + 1)) (f := x)

end Lemmata.FrankWolfePS.Hilbert
