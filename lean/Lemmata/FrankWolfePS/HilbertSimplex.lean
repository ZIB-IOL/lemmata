module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The countable subprobability simplex and exact changes of a separable support objective. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert

open Finset Set
open scoped BigOperators Topology

/-- The closed subprobability simplex, in the topology of coordinatewise convergence. -/
def simplex : Set (ℕ → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ s : Finset ℕ, ∑ i ∈ s, x i ≤ 1}

theorem simplex_zero : (0 : ℕ → ℝ) ∈ simplex := by
  constructor <;> simp

theorem coord_le_one {x : ℕ → ℝ} (hx : x ∈ simplex) (i : ℕ) : x i ≤ 1 := by
  simpa using hx.2 {i}

theorem mass_summable {x : ℕ → ℝ} (hx : x ∈ simplex) : Summable x :=
  summable_of_sum_le hx.1 hx.2

theorem mass_le_one {x : ℕ → ℝ} (hx : x ∈ simplex) : ∑' i, x i ≤ 1 :=
  (mass_summable hx).tsum_le_of_sum_le hx.2

theorem mem_simplex_of_hasSum {x : ℕ → ℝ} {s : ℝ} (hx : ∀ i, 0 ≤ x i)
    (hs : HasSum x s) (h1 : s ≤ 1) : x ∈ simplex :=
  ⟨hx, fun F => (hs.summable.sum_le_tsum F (fun i _ => hx i)).trans (hs.tsum_eq ▸ h1)⟩

theorem simplex_compact : IsCompact simplex := by
  have eq : simplex = (⋂ i : ℕ, {x : ℕ → ℝ | 0 ≤ x i}) ∩
      ⋂ s : Finset ℕ, {x : ℕ → ℝ | ∑ i ∈ s, x i ≤ 1} := by ext x; simp [simplex]
  have cl : IsClosed simplex := by
    rw [eq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_iInter fun s => isClosed_le (by fun_prop) continuous_const)
  apply (isCompact_Icc (a := (0 : ℕ → ℝ)) (b := 1)).of_isClosed_subset cl
  exact fun x hx => ⟨hx.1, coord_le_one hx⟩

/-- Linear minus diagonal quadratic support objective on the simplex. -/
noncomputable def score (l b x : ℕ → ℝ) : ℝ := ∑' i, (l i * x i - b i * (x i)^2)

theorem terms_summable {l b x : ℕ → ℝ} {M : ℝ} (hx : x ∈ simplex)
    (hM : ∀ i, |l i| + |b i| ≤ M) : Summable (fun i => l i * x i - b i * (x i)^2) := by
  apply ((mass_summable hx).mul_left M).of_norm_bounded
  intro i
  have lo := hx.1 i
  have hi := coord_le_one hx i
  have sq : (x i)^2 ≤ x i := by nlinarith [mul_nonneg lo (sub_nonneg.mpr hi)]
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |l i * x i| + |b i * (x i)^2| := abs_sub _ _
    _ = |l i| * x i + |b i| * (x i)^2 := by
      simp only [abs_mul, abs_of_nonneg lo, abs_of_nonneg (sq_nonneg (x i))]
    _ ≤ (|l i| + |b i|) * x i := by
      rw [add_mul]; linarith [mul_le_mul_of_nonneg_left sq (abs_nonneg (b i))]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hM i) lo

/-- Change a single coordinate by a signed amount. -/
def bump (x : ℕ → ℝ) (j : ℕ) (t : ℝ) (i : ℕ) := x i + if i = j then t else 0

theorem bump_hasSum {x : ℕ → ℝ} {s : ℝ} (hx : HasSum x s) (j : ℕ) (t : ℝ) :
    HasSum (bump x j t) (s+t) := hx.add (hasSum_ite_eq j t)

theorem term_bump_hasSum {l b x : ℕ → ℝ} {v : ℝ}
    (h : HasSum (fun i => l i * x i - b i * (x i)^2) v) (j : ℕ) (t : ℝ) :
    HasSum (fun i => l i * bump x j t i - b i * (bump x j t i)^2)
      (v + t * (l j - b j * (2*x j+t))) := by
  apply (h.add (hasSum_ite_eq j (t * (l j - b j * (2*x j+t))))).congr_fun
  intro i
  by_cases eq : i = j
  · subst i; simp [bump]; ring
  · simp [bump, eq]

/-- When one coordinate has a positive marginal even at mass one and dominates all later
marginals at zero, every global maximizer has full mass on the initial prefix. -/
theorem maximizer_prefix {l b x : ℕ → ℝ} {J : ℕ}
    (hx : x ∈ simplex) (hs : Summable (fun i => l i * x i - b i * (x i)^2))
    (opt : IsMaxOn (score l b) simplex x) (hb : ∀ i, 0 ≤ b i)
    (pos : 0 < l J - 2*b J) (sep : ∀ j, J < j → l j < l J - 2*b J) :
    (∀ j, J < j → x j = 0) ∧ ∑ i ∈ range (J+1), x i = 1 := by
  have hm := mass_summable hx
  have total := mass_le_one hx
  have cost : HasSum (fun i => l i*x i-b i*(x i)^2) (score l b x) := hs.hasSum
  have upper := isMaxOn_iff.mp opt
  have tail (j : ℕ) (hj : J < j) : x j = 0 := by
    by_contra ne
    have posj : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm ne)
    have neq : j ≠ J := Nat.ne_of_gt hj
    let y := bump x j (-(x j))
    let z := bump y J (x j)
    have hy : HasSum y ((∑' i, x i) + -(x j)) := bump_hasSum hm.hasSum _ _
    have hz : HasSum z (∑' i, x i) := by simpa using bump_hasSum hy J (x j)
    have mem : z ∈ simplex := by
      apply mem_simplex_of_hasSum _ hz total
      intro i
      by_cases a : i = j
      · subst i; simp [z, y, bump, neq]
      · by_cases c : i = J
        · subst i; simpa [z, y, bump, Ne.symm neq] using add_nonneg (hx.1 J) posj.le
        · simpa [z, y, bump, a, c] using hx.1 i
    have yJ : y J = x J := by simp [y, bump, Ne.symm neq]
    have sumle : x J + x j ≤ 1 := by
      simpa [z, bump, yJ] using coord_le_one mem J
    have gain := (term_bump_hasSum (term_bump_hasSum cost j (-(x j))) J (x j)).tsum_eq
    change score l b z = _ at gain
    simp only [bump, ite_eq_right (Ne.symm neq), add_zero] at gain
    have recv : b J * (2*x J+x j) ≤ 2*b J := by
      nlinarith [mul_le_mul_of_nonneg_left sumle (hb J), mul_nonneg (hb J) posj.le]
    have dom : 0 < (l J - b J*(2*x J+x j)) - (l j - b j*x j) := by
      linarith [sep j hj, mul_nonneg (hb j) posj.le]
    nlinarith [upper z mem, mul_pos posj dom]
  have finiteSum : (∑' i, x i) = ∑ i ∈ range (J+1), x i := by
    apply tsum_eq_sum
    intro i hi
    exact tail i (by simpa using hi)
  refine ⟨tail, ?_⟩
  rw [← finiteSum]
  apply le_antisymm total
  by_contra! lt
  let t := 1 - ∑' i, x i
  have ht : 0 < t := sub_pos.mpr lt
  let z := bump x J t
  have hz : HasSum z 1 := by
    convert bump_hasSum hm.hasSum J t using 1
    dsimp [t]
    ring
  have mem : z ∈ simplex := by
    apply mem_simplex_of_hasSum _ hz le_rfl
    intro i
    by_cases eq : i = J
    · subst i; simpa [z,bump] using add_nonneg (hx.1 J) ht.le
    · simpa [z,bump,eq] using hx.1 i
  have sumle : x J+t ≤ 1 := by simpa [z,bump] using coord_le_one mem J
  have recv : b J*(2*x J+t) ≤ 2*b J := by
    nlinarith [mul_le_mul_of_nonneg_left sumle (hb J), mul_nonneg (hb J) ht.le]
  have gain := (term_bump_hasSum cost J t).tsum_eq
  change score l b z = _ at gain
  linarith [upper z mem, mul_pos ht (show 0 < l J-b J*(2*x J+t) by linarith)]

end Lemmata.FrankWolfePS.Hilbert
