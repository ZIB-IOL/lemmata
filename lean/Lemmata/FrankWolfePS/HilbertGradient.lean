module

public import Lemmata.FrankWolfePS.HilbertGram
public import Lemmata.FrankWolfePS.HilbertSupport

/-! The exact infinite support problem and the gradient-directed hull trajectory in Gram coordinates. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped Topology BigOperators

noncomputable def penalty (Q : ℝ) (i : ℕ) : ℝ := Q/100 * (weight i)^2
noncomputable def linearTerm (x : ℕ → ℝ) (G Q : ℝ) (i : ℕ) : ℝ :=
  -gram x i - G*(weight i)^2 + penalty Q i

theorem penalty_limit (Q : ℝ) : Tendsto (penalty Q) atTop (𝓝 0) := by
  unfold penalty
  simpa using (weight_limit.pow 2).const_mul (Q/100)

theorem linearTerm_limit {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0) (G Q : ℝ) :
    Tendsto (linearTerm x G Q) atTop (𝓝 0) := by
  have h := ((weight_limit.const_mul (∑ i ∈ range n, x i)).sub
    ((weight_limit.pow 2).const_mul G)).add (penalty_limit Q)
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop n] with i hi
  simp [linearTerm, gram_tail hx hi]

/-- The unique optimizer for the actual countable quadratic support problem at any finite chart. -/
theorem unique_gradient_parameter {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0)
    (G : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∃! u, u ∈ simplex ∧ IsMaxOn (score (linearTerm x G Q) (penalty Q)) simplex u :=
  unique_parameter (linearTerm_limit hx G Q) (penalty_limit Q) (fun i => by
    have := weight_pos i; unfold penalty; positivity)

/-- The exact parameter of a gradient reply fills the prefix plus one coordinate.
The maximization is over the full countable simplex. -/
theorem gradient_prefix {n : ℕ} {x u : ℕ → ℝ} {G Q : ℝ}
    (hx : x ∈ prefixSlice n) (hG₀ : 3 ≤ G) (hG₁ : G ≤ 6) (hQ₀ : 0 < Q) (hQ₁ : Q ≤ 7)
    (hu : u ∈ simplex) (opt : IsMaxOn (score (linearTerm x G Q) (penalty Q)) simplex u) :
    (∀ j, n < j → u j = 0) ∧ ∑ i ∈ range (n+1), u i = 1 := by
  let m := ∑ i ∈ range n, x i
  have hm : 1/2 ≤ m := hx.2.1
  have hmpos : 0 < m := by linarith
  have wk := weight_small n
  have kpos : 0 ≤ G+Q/100 := by linarith
  have small : (G+Q/100)*weight n < m/2 := by
    nlinarith [mul_le_mul_of_nonneg_left wk kpos]
  have next : linearTerm x G Q n - 2*penalty Q n = m*weight n - (G+Q/100)*(weight n)^2 := by
    simp [linearTerm, penalty, gram_tail hx.1 (le_refl n),m]; ring
  apply maximizer_prefix hu (null_terms_summable (linearTerm_limit hx.1 G Q) (penalty_limit Q) hu) opt
  · intro i; unfold penalty; positivity
  · rw [next]
    exact lt_of_le_of_lt (by simp : 0 ≤ m*0) (next_strict m (weight n) 0 (G+Q/100)
      hmpos (weight_pos _) (by have := weight_pos n; linarith) small)
  · intro j hj
    rw [next]
    apply lt_of_le_of_lt _ (next_strict m (weight n) (weight j) (G+Q/100) hmpos
      (weight_pos _) (weight_half hj) small)
    simp only [linearTerm, penalty, gram_tail hx.1 hj.le, neg_mul, neg_neg]
    change m * weight j - G * (weight j)^2 + Q/100 * (weight j)^2 ≤ _
    nlinarith [mul_nonneg (show 0 ≤ G-Q/100 by linarith) (sq_nonneg (weight j))]

/-- A canonical selector for the countable exact oracle. The fallback is unused on a prefix. -/
noncomputable def gradientParameter (x : ℕ → ℝ) (G Q : ℝ) : ℕ → ℝ :=
  open Classical in
  if h : ∃ u, u ∈ simplex ∧ IsMaxOn (score (linearTerm x G Q) (penalty Q)) simplex u
  then Classical.choose h else 0

theorem gradientParameter_spec {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i = 0)
    (G : ℝ) {Q : ℝ} (hQ : 0 < Q) : gradientParameter x G Q ∈ simplex ∧
    IsMaxOn (score (linearTerm x G Q) (penalty Q)) simplex (gradientParameter x G Q) := by
  have h := (unique_gradient_parameter hx G hQ).exists
  simpa [gradientParameter, dite_eq_left h] using Classical.choose_spec h

/-- Horizontal chart of the support point, including the radius divided by the gradient norm. -/
noncomputable def gradientReply (x : ℕ → ℝ) (G Q d : ℝ) (i : ℕ) : ℝ :=
  gradientParameter x G Q i - d*x i

theorem gradientReply_mem {n : ℕ} {x : ℕ → ℝ} {G Q d : ℝ} (hx : x ∈ prefixSlice n)
    (hG₀ : 3 ≤ G) (hG₁ : G ≤ 6) (hQ₀ : 0 < Q) (hQ₁ : Q ≤ 7) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 2/5) :
    gradientReply x G Q d ∈ prefixSlice (n+1) := by
  obtain ⟨hu,ho⟩ := gradientParameter_spec hx.1 G hQ₀
  obtain ⟨hz,hm⟩ := gradient_prefix hx hG₀ hG₁ hQ₀ hQ₁ hu ho
  refine ⟨fun i hi => by simp [gradientReply, hz i (by omega), hx.1 i (by omega)], ?_⟩
  simp only [gradientReply, sum_sub_distrib, ← mul_sum, hm]
  rw [sum_range_succ (f:=x), hx.1 n (le_refl n), add_zero]
  exact reply_mass _ _ hx.2.1 hx.2.2 hd₀ hd₁

/-- Full trajectory reduction for gradient-directed hull methods. The kernel verifies the
infinite maximizations and the energy estimate for all times, for every admissible scalar trace. -/
theorem gradient_hull_energy (seed : ℕ → ℝ) (query reply : ℕ → ℕ → ℝ) (G Q d : ℕ → ℝ)
    (hs : seed ∈ prefixSlice 1)
    (hq : ∀ t, query t ∈ convexHull ℝ (insert seed (reply '' Set.Iio t)))
    (hg : ∀ t, 3 ≤ G t ∧ G t ≤ 6 ∧ 0 < Q t ∧ Q t ≤ 7 ∧ 0 ≤ d t ∧ d t ≤ 2/5)
    (hr : ∀ t, reply t = gradientReply (query t) (G t) (Q t) (d t))
    (t : ℕ) (x : ℕ → ℝ) (hx : x ∈ convexHull ℝ (insert seed (reply '' Set.Iio t))) :
    31 / (256 * ((t:ℝ)+1)) ≤ energy x / 2 := by
  have r := hull_after_queries seed query reply hs hq (fun k h => by
    rcases hg k with ⟨g₀,g₁,q₀,q₁,d₀,d₁⟩
    rw [hr]; exact gradientReply_mem h g₀ g₁ q₀ q₁ d₀ d₁) t hx
  exact prefix_gap t x _ r (by linarith [energy_lower r.1])

end Lemmata.FrankWolfePS.Hilbert
