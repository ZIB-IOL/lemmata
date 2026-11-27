module
public import Lemmata.FrankWolfePS.HilbertGram
public import Lemmata.FrankWolfePS.HilbertSimplex
public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-! A real Hilbert realization of the infinite Gram matrix by the positive-kernel construction. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped RealInnerProductSpace BigOperators Topology

noncomputable def entry (i j : ℕ) : ℝ := (if i=j then 1 else 0) - weight (max i j)

theorem entry_symm (i j : ℕ) : entry i j = entry j i := by simp [entry, eq_comm, max_comm]

theorem entry_row {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i=0) (j : ℕ) :
    ∑ i ∈ range n, x i * entry i j = gram x j := by
  rw [gram_prefix hx]
  simp only [entry, mul_sub, sum_sub_distrib]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range]
  split <;> simp_all

noncomputable def realKernel : Matrix ℕ ℕ (ℝ →L[ℝ] ℝ) :=
  fun i j => entry i j • ContinuousLinearMap.id ℝ ℝ

private theorem kernel_psd : realKernel.PosSemidef := by
  apply RKHS.posSemidef_iff_re_sum_kernel'.2
  constructor
  · ext i j
    simp [Matrix.conjTranspose_apply, realKernel, star, ContinuousLinearMap.adjoint_id, entry_symm j i]
  · intro f
    let n := f.support.sup id + 1
    have hs : f.support ⊆ range n := fun i hi => mem_range.mpr (Nat.lt_succ_of_le (le_sup (f:=id) hi))
    have hz (i : ℕ) (hi : n ≤ i) : f i = 0 := by
      by_contra hn
      exact Nat.not_lt_of_ge hi (mem_range.mp (hs (Finsupp.mem_support_iff.mpr hn)))
    have en := energy_lower hz
    have nn : 0 ≤ energy f := by
      have := sum_nonneg (s:=range n) (fun i _ => sq_nonneg (f i)); linarith
    have e : energy f = ∑ i ∈ range n, f i * gram f i := by
      unfold energy
      exact tsum_eq_sum (fun i hi => by simp [hz i (by simpa using hi)])
    rw [e] at nn
    simp only [realKernel, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, real_inner_comm, RCLike.re_to_real]
    rw [f.sum_of_support_subset hs _ (by simp)]
    convert nn using 1
    apply sum_congr rfl
    intro i _
    rw [f.sum_of_support_subset hs _ (by simp), ← entry_row hz, mul_sum]
    apply sum_congr rfl
    intro j _
    simp [mul_comm, mul_left_comm]

instance : Fact realKernel.PosSemidef := ⟨kernel_psd⟩

/-- A genuine complete real inner-product space for the horizontal coordinates. -/
abbrev Horizontal := RKHS.OfKernel realKernel

noncomputable def axis (i : ℕ) : Horizontal := RKHS.kerFun Horizontal i 1

/-- Inner products of the actual Hilbert vectors realize the prescribed Gram entries. -/
theorem axis_inner (i j : ℕ) : ⟪axis i, axis j⟫ = entry i j := by
  have e := RKHS.kernel_inner Horizontal j i (1:ℝ) 1
  rw [RKHS.OfKernel.kernel_ofKernel] at e
  change ⟪RKHS.kerFun Horizontal i 1, RKHS.kerFun Horizontal j 1⟫ = _
  rw [← e]
  simp [realKernel,entry_symm j i]

theorem axis_norm_sq (i : ℕ) : ‖axis i‖^2 = 1-weight i := by
  rw [← real_inner_self_eq_norm_sq, axis_inner]; simp [entry]

theorem axis_norm_le (i : ℕ) : ‖axis i‖ ≤ 1 := by nlinarith [axis_norm_sq i, weight_pos i]


/-- Hilbert synthesis, absolutely convergent at every simplex parameter and exact on finite charts. -/
noncomputable def synth (x : ℕ → ℝ) : Horizontal := ∑' i, x i • axis i

theorem synth_summable {x : ℕ → ℝ} (hx : x ∈ simplex) : Summable (fun i => x i • axis i) := by
  apply (mass_summable hx).of_norm_bounded
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
  simpa using mul_le_mul_of_nonneg_left (axis_norm_le i) (hx.1 i)

theorem norm_synth_le {x : ℕ → ℝ} (hx : x ∈ simplex) : ‖synth x‖ ≤ 1 := by
  have bd (i) : ‖x i • axis i‖ ≤ x i := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
    simpa using mul_le_mul_of_nonneg_left (axis_norm_le i) (hx.1 i)
  have sm := (mass_summable hx).of_nonneg_of_le (fun i => norm_nonneg _) bd
  exact (norm_tsum_le_tsum_norm sm).trans ((sm.tsum_le_tsum bd (mass_summable hx)).trans (mass_le_one hx))

theorem synth_finite {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i=0) :
    synth x = ∑ i ∈ range n, x i • axis i :=
  tsum_eq_sum (fun i hi => by simp [hx i (by simpa using hi)])

theorem synth_inner_axis {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i=0) (j : ℕ) :
    ⟪synth x, axis j⟫ = gram x j := by
  rw [synth_finite hx, sum_inner]
  simpa only [real_inner_smul_left, axis_inner] using entry_row hx j

theorem synth_energy {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, n ≤ i → x i=0) :
    ‖synth x‖^2 = energy x := by
  rw [← real_inner_self_eq_norm_sq]
  nth_rw 2 [synth_finite hx]
  rw [inner_sum]
  simp only [real_inner_smul_right, synth_inner_axis hx]
  exact (tsum_eq_sum (fun i hi => by simp [hx i (by simpa using hi)])).symm

/-- The Hilbert atoms are weakly null, including against test vectors outside any finite hull. -/
theorem axis_null (q : Horizontal) : Tendsto (fun i => ⟪q, axis i⟫) atTop (𝓝 0) := by
  let c := fun i => ⟪q, axis i⟫
  have bs (n : ℕ) : ∑ i ∈ range n, (c i)^2 ≤ 2*‖q‖^2 := by
    let x := fun i => if i<n then c i else 0
    have hz (i : ℕ) (hi : n ≤ i) : x i=0 := by simp [x,not_lt.mpr hi]
    have eq : ∑ i ∈ range n, (x i)^2 = ∑ i ∈ range n, (c i)^2 :=
      sum_congr rfl fun i hi => by simp [x,mem_range.mp hi]
    have dot : ⟪q,synth x⟫ = ∑ i ∈ range n, (c i)^2 := by
      rw [synth_finite hz, inner_sum]
      apply sum_congr rfl
      intro i hi; simp [real_inner_smul_right, x, mem_range.mp hi, c, sq]
    have up := energy_upper hz
    rw [←synth_energy hz,eq] at up
    have cs := real_inner_le_norm q (synth x)
    rw [dot] at cs
    nlinarith [sq_nonneg (‖synth x‖-‖q‖)]
  have lim := (summable_of_sum_range_le (fun i => sq_nonneg (c i)) bs).tendsto_atTop_zero
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp lim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Function.comp_def,Real.sqrt_sq_eq_abs, Real.norm_eq_abs, c] using h

open Set Submodule

/-- The concrete horizontal realization is separable in its norm topology. -/
theorem horizontal_separable : TopologicalSpace.SeparableSpace Horizontal := by
  let S := Submodule.span ℝ (Set.range axis)
  have e : S.topologicalClosure=⊤ := by
    apply top_unique
    rw [←RKHS.kerFun_dense Horizontal]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro z ⟨i,v,rfl⟩
    have hv : RKHS.kerFun Horizontal i v=v • axis i := by
      rw [axis,←map_smul,smul_eq_mul,mul_one]
    rw [hv]
    exact S.smul_mem v (Submodule.subset_span ⟨i,rfl⟩)
  have h := ((Set.countable_range axis).isSeparable.span (R:=ℝ)).closure
  change TopologicalSpace.IsSeparable (closure (S : Set Horizontal)) at h
  rw [←S.topologicalClosure_coe,e] at h
  exact TopologicalSpace.isSeparable_univ_iff.mp h

/-- In finite dimension weak nullity and compactness of the unit ball would force a norm-null
subsequence of the axes, contrary to their Gram diagonal. -/
theorem horizontal_infinite : ¬FiniteDimensional ℝ Horizontal := by
  intro fd
  let : FiniteDimensional ℝ Horizontal := fd
  let : ProperSpace Horizontal := FiniteDimensional.proper ℝ Horizontal
  obtain ⟨u,_,f,hf,lim⟩ := (isCompact_closedBall (0:Horizontal) 1).tendsto_subseq
    (fun i => show axis i∈Metric.closedBall 0 1 by simpa [Metric.mem_closedBall] using axis_norm_le i)
  have dot := ((innerSL ℝ u).continuous.continuousAt.tendsto.comp lim)
  have nu := (axis_null u).comp hf.tendsto_atTop
  have eq : ⟪u,u⟫=0 := tendsto_nhds_unique dot nu
  have uz : u=0 := by simpa using eq
  subst u
  have nl := lim.norm
  simp only [norm_zero] at nl
  obtain ⟨N,hN⟩ := eventually_atTop.mp (nl (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  have sm : ‖axis (f N)‖ < 1/2 := hN N le_rfl
  nlinarith [axis_norm_sq (f N),weight_small (f N), norm_nonneg (axis (f N))]


end Lemmata.FrankWolfePS.Hilbert
