module

public import Lemmata.FrankWolfePS.HilbertSimplex
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Attainment and uniqueness for both countable lifted-simplex support problems. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Filter Finset Set
open scoped Topology BigOperators

private theorem null_bounded {l b : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) : ∃ M, ∀ i, |l i|+|b i| ≤ M := by
  have lim : Tendsto (fun i => |l i|+|b i|) atTop (𝓝 0) := by simpa using hl.abs.add hb.abs
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ lim).exists_norm_le
  refine ⟨M, fun i => ?_⟩
  have bound : ‖|l i|+|b i|‖ ≤ M := hM _ ⟨i,rfl⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg (l i)) (abs_nonneg (b i)))] using bound

theorem null_terms_summable {l b x : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hx : x ∈ simplex) :
    Summable (fun i => l i*x i-b i*(x i)^2) := by
  obtain ⟨M, hM⟩ := null_bounded hl hb
  exact terms_summable hx hM

/-- Uniform convergence on the entire simplex for coefficient sequences tending to zero.
The linear coefficients need not be absolutely summable. -/
theorem score_continuousOn {l b : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) : ContinuousOn (score l b) simplex := by
  let f (i : ℕ) (x : ℕ → ℝ) := l i*x i-b i*(x i)^2
  have lim : Tendsto (fun i => |l i|+|b i|) atTop (𝓝 0) := by simpa using hl.abs.add hb.abs
  have uniform : TendstoUniformlyOn (fun n x => ∑ i ∈ range n, f i x) (score l b) atTop simplex := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (lim (Iio_mem_nhds (half_pos hε)))
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx
    have hxsum := mass_summable hx
    have hc := null_terms_summable hl hb hx
    have tail := (summable_nat_add_iff n).2 hc
    have mass := (summable_nat_add_iff n).2 hxsum
    have bd (i : ℕ) : ‖f (i+n) x‖ ≤ ε/2*x (i+n) := by
      have z := hx.1 (i+n)
      have u := coord_le_one hx (i+n)
      have bnd : |l (i+n)|+|b (i+n)| < ε/2 := hN (i+n) (by omega)
      change |l (i+n)*x (i+n)-b (i+n)*(x (i+n))^2| ≤ _
      calc
        _ ≤ |l (i+n)*x (i+n)|+|b (i+n)*(x (i+n))^2| := abs_sub _ _
        _ ≤ (|l (i+n)|+|b (i+n)|)*x (i+n) := by
          simp only [abs_mul, abs_of_nonneg z, abs_of_nonneg (sq_nonneg (x (i+n))), add_mul]
          nlinarith [mul_le_mul_of_nonneg_left (show (x (i+n))^2 ≤ x (i+n) by
            nlinarith [mul_nonneg z (sub_nonneg.mpr u)]) (abs_nonneg (b (i+n)))]
        _ ≤ _ := mul_le_mul_of_nonneg_right bnd.le z
    have massle : (∑' i, x (i+n)) ≤ 1 := by
      linarith [hxsum.sum_add_tsum_nat_add n, mass_le_one hx, sum_nonneg (s:=range n) (fun i _ => hx.1 i)]
    have normtail : ‖∑' i, f (i+n) x‖ ≤ ε/2 := calc
      _ ≤ ∑' i, ‖f (i+n) x‖ := norm_tsum_le_tsum_norm tail.abs
      _ ≤ ∑' i, ε/2*x (i+n) := Summable.tsum_le_tsum bd tail.abs (mass.mul_left _)
      _ = ε/2*(∑' i, x (i+n)) := tsum_mul_left
      _ ≤ ε/2 := by nlinarith [mul_le_mul_of_nonneg_left massle (half_pos hε).le]
    have eq : score l b x - ∑ i ∈ range n, f i x = ∑' i, f (i+n) x := by
      have H := hc.sum_add_tsum_nat_add n
      change (∑ i ∈ range n, f i x) + (∑' i, f (i+n) x) = score l b x at H
      linarith
    rw [dist_eq_norm, eq]
    exact normtail.trans_lt (half_lt_self hε)
  apply uniform.continuousOn
  exact Frequently.of_forall fun n => by dsimp [f]; fun_prop

private theorem midpoint_mem {x y : ℕ → ℝ} (hx : x ∈ simplex) (hy : y ∈ simplex) :
    (fun i => (x i+y i)/2) ∈ simplex := by
  refine ⟨fun i => by have := hx.1 i; have := hy.1 i; linarith, fun s => ?_⟩
  simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib]
  linarith [hx.2 s, hy.2 s]

/-- Every such diagonal support problem with strictly positive quadratic penalties has
exactly one optimizer, including in directions involving infinitely many coordinates. -/
theorem unique_parameter {l b : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hp : ∀ i, 0 < b i) :
    ∃! x, x ∈ simplex ∧ IsMaxOn (score l b) simplex x := by
  obtain ⟨x,hx,hmax⟩ := simplex_compact.exists_isMaxOn ⟨0,simplex_zero⟩ (score_continuousOn hl hb)
  refine ⟨x, ⟨hx,hmax⟩, ?_⟩
  rintro y ⟨hy,hymax⟩
  by_contra ne
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ x j := by simpa [funext_iff] using ne
  let z := fun i => (x i+y i)/2
  have hz : z ∈ simplex := midpoint_mem hx hy
  let f := fun (u : ℕ → ℝ) i => l i * u i - b i * (u i)^2
  have mid (i) : 2*f z i-(f x i+f y i) = b i*((x i-y i)^2)/2 := by dsimp [f,z]; ring
  have strict := Summable.tsum_lt_tsum (f := fun i => f x i+f y i) (g := fun i => 2*f z i)
    (i:=j) (fun i => by linarith [mid i, mul_nonneg (hp i).le (sq_nonneg (x i-y i))])
    (by linarith [mid j, mul_pos (hp j) (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hj)))])
    ((null_terms_summable hl hb hx).add (null_terms_summable hl hb hy))
    ((null_terms_summable hl hb hz).mul_left 2)
  have add := (null_terms_summable hl hb hx).tsum_add (null_terms_summable hl hb hy)
  change (∑' i, (f x i + f y i)) = score l b x + score l b y at add
  rw [add, tsum_mul_left] at strict
  change score l b x + score l b y < 2*score l b z at strict
  linarith [isMaxOn_iff.mp hmax z hz, isMaxOn_iff.mp hymax z hz]

theorem simplex_mix {u v : ℕ → ℝ} (hu : u∈simplex) (hv : v∈simplex)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    (fun i => a*u i+b*v i)∈simplex := by
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i)),fun s => ?_⟩
  simp only [sum_add_distrib,←mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left (hu.2 s) ha,mul_le_mul_of_nonneg_left (hv.2 s) hb]

/-- Concavity on the entire countable simplex, with no summability of the coefficients required. -/
theorem score_concave {l p u v : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 0))
    (hn : ∀ i,0≤p i) (hu : u∈simplex) (hv : v∈simplex) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a*score l p u+b*score l p v ≤ score l p (fun i => a*u i+b*v i) := by
  let w := fun i => a*u i+b*v i
  let g := fun (x : ℕ → ℝ) i => l i*x i-p i*(x i)^2
  have sm (x : ℕ → ℝ) (hx : x∈simplex) : Summable (g x) := null_terms_summable hl hp hx
  have le (i) : a*g u i+b*g v i ≤ g w i := by
    have e : g w i-(a*g u i+b*g v i)=p i*a*b*(u i-v i)^2 := by
      dsimp [g,w]; rw [show b=1-a by linarith]; ring
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (hn i) ha) hb) (_root_.sq_nonneg (u i-v i))]
  have base := ((sm u hu).mul_left a).add ((sm v hv).mul_left b)
  have e := base.tsum_le_tsum le (sm w (simplex_mix hu hv ha hb hab))
  rw [((sm u hu).mul_left a).tsum_add ((sm v hv).mul_left b),tsum_mul_left,tsum_mul_left] at e
  exact e

end Lemmata.FrankWolfePS.Hilbert
