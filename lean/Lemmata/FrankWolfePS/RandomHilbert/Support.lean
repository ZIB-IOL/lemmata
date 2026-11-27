module
public import Lemmata.FrankWolfePS.RandomHilbert.Prior
/-! Every parameter yields a body in the Hausdorff support of the same prior. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators
noncomputable def remaining (n : ℕ) := ∑' i,energy (i+n)
private theorem remainder_nonneg (n) : 0≤remaining n := tsum_nonneg (fun _ => (energy_pos _).le)
private theorem tail_bound {f : ℕ → ℝ} (n : ℕ) (sf : Summable f)
    (zero : ∀ i<n,f i=0) {c : ℝ} (b : ∀ i, f i≤c*energy i) : ∑' i,f i≤c*remaining n := by
  have h := sf.sum_add_tsum_nat_add n
  rw [sum_eq_zero (fun i hi => zero i (mem_range.mp hi)),zero_add] at h
  rw [←h]; unfold remaining; rw [←tsum_mul_left]
  exact ((summable_nat_add_iff n).mpr sf).tsum_le_tsum (fun i => b (i+n))
    (((summable_nat_add_iff n).mpr sum_energy).mul_left c)

private theorem move_point (x y : Tape) (n : ℕ) (same : ∀ i<n,x i=y i)
    {p : World} (hp : p∈body (data x)) :
    ∃ q∈body (data y),dist p q≤Real.sqrt (4*remaining n)+remaining n := by
  classical
  obtain ⟨u,hu⟩ := hp
  let v : Param (data y) := fun i => if h : i<n then
    ⟨(u i).val,by simpa only [data,←same i h] using (u i).property⟩
    else (seedPar (data y)) i
  have eq (i) (hi : i<n) : (v i).val=(u i).val := by simp [v,hi]
  have blocks {d : Data} (a : Param d) (i : ℕ) : ‖horizontal a i‖≤amp i := by
    rw [horizontal_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (amp_pos _)]
    exact mul_le_of_le_one_right (amp_pos _).le (lift_norm (a i).property)
  have hs := tail_bound n (sq_blocks_sm (horizontal u-horizontal v))
    (fun i hi => by simp only [lp.coeFn_sub,Pi.sub_apply,horizontal_apply,eq i hi,sub_self,norm_zero]; norm_num)
    (c:=4) (fun i => by
      change ‖horizontal u i-horizontal v i‖^2≤4*energy i
      have t := pow_le_pow_left₀ (norm_nonneg _) (show ‖horizontal u i-horizontal v i‖≤2*amp i by
        linarith [norm_sub_le (horizontal u i) (horizontal v i),blocks u i,blocks v i]) 2
      nlinarith only [t,amp_sq i])
  rw [←norm_sq_sum] at hs
  have hc : ‖ctr u-ctr v‖≤Real.sqrt (4*remaining n) := by
    have e : ctr u-ctr v=WithLp.toLp 2 ((0:ℝ),horizontal u-horizontal v) := by
      apply WithLp.ofLp_injective; apply Prod.ext <;> simp [ctr]
    rw [e,WithLp.norm_toLp_snd]
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (by norm_num) (remainder_nonneg n))).mpr hs
  let f := fun i => bonus (data x i).1 (u i).val-bonus (data y i).1 (v i).val
  have r0 (i) (hi : i<n) : f i=0 := by simp only [f,eq i hi,data,same i hi,sub_self]
  have upper (i) : f i≤1*energy i := by
    have a := (bonus_bound (D:=(data x i).1) (u i).property).2.trans (eta_le i)
    dsimp [f]; linarith [(bonus_bound (D:=(data y i).1) (v i).property).1,energy_pos i]
  have lower (i) : -f i≤1*energy i := by
    have a := (bonus_bound (D:=(data y i).1) (v i).property).2.trans (eta_le i)
    dsimp [f]; linarith [(bonus_bound (D:=(data x i).1) (u i).property).1,energy_pos i]
  have sm : Summable f := (bonus_sm u).sub (bonus_sm v)
  have high := tail_bound n sm r0 upper
  have low := tail_bound n sm.neg (fun i hi => by simp [r0 i hi]) lower
  rw [tsum_neg] at low
  have rf : rad u-rad v=∑' i,f i := by unfold rad f; rw [(bonus_sm u).tsum_sub (bonus_sm v)]; ring
  have rb : |rad u-rad v|≤remaining n := abs_le.mpr ⟨by linarith,by linarith⟩
  let z := (rad u)⁻¹ • (p-ctr u)
  have rp : 0<rad u := by linarith [(rad_bounds u).1]
  have zn : ‖z‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp),inv_mul_le_iff₀ rp,mul_one]; exact hu
  have pz : p=ctr u+rad u • z := by simp [z,smul_smul,rp.ne']
  let q := ctr v+rad v • z
  refine ⟨q,⟨v,?_⟩,?_⟩
  · have rp' : 0≤rad v := by linarith [(rad_bounds v).1]
    simpa [q,norm_smul,Real.norm_eq_abs,abs_of_nonneg rp'] using mul_le_of_le_one_right rp' zn
  · have eq' : p-q=(ctr u-ctr v)+(rad u-rad v) • z := by rw [pz]; dsimp [q]; rw [sub_smul]; abel
    rw [dist_eq_norm,eq']
    have tri := norm_add_le (ctr u-ctr v) ((rad u-rad v) • z)
    rw [norm_smul,Real.norm_eq_abs] at tri
    linarith [mul_le_of_le_one_right (abs_nonneg (rad u-rad v)) zn]

/-- A positive-measure cylinder fits in every Hausdorff neighbourhood of the realized body.
This formulation gives support directly, without choosing a coding of arbitrary closed sets. -/
theorem hausdorff_support (x : Tape) {ε : ℝ} (hp : 0<ε) :
    ∃ E : Set Tape, MeasurableSet E ∧ 0<prior E ∧
      ∀ y∈E,Metric.hausdorffDist (body (data x)) (body (data y))<ε := by
  have z : Tendsto remaining atTop (𝓝 0) := tendsto_sum_nat_add energy
  have lim : Tendsto (fun n => Real.sqrt (4*remaining n)+remaining n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero,zero_add] using ((Real.continuous_sqrt.tendsto 0).comp (by simpa using z.const_mul 4)).add z
  obtain ⟨n,hn⟩ := (lim.eventually_lt_const hp).exists
  let E := Set.pi (↑(range n) : Set ℕ) (fun i => {x i})
  have me : MeasurableSet E := MeasurableSet.pi (range n).countable_toSet (fun i _ => measurableSet_singleton _)
  refine ⟨E,me,?_,?_⟩
  · change 0<Measure.infinitePi marginal ((↑(range n) : Set ℕ).pi (fun i => {x i}))
    rw [Measure.infinitePi_pi marginal (fun i _ => measurableSet_singleton _)]
    apply pos_iff_ne_zero.mpr; apply Finset.prod_ne_zero_iff.mpr; intro i _
    rw [marginal,Measure.uniformOfFinset_apply_singleton]; simp only [mem_univ,ite_true,card_univ,ENNReal.inv_ne_zero]; finiteness
  · intro y hy
    have he (i) (hi : i<n) : y i=x i := hy i (mem_range.mpr hi)
    exact (Metric.hausdorffDist_le_of_mem_dist (add_nonneg (Real.sqrt_nonneg _) (remainder_nonneg n))
      (fun _ ht => move_point x y n (fun i hi => (he i hi).symm) ht)
      (fun _ ht => by
        obtain ⟨z,hz,dist⟩ := move_point y x n he ht
        exact ⟨z,hz,by simpa [dist_comm] using dist⟩)).trans_lt hn
end Lemmata.FrankWolfePS.RandomHilbert
