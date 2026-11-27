module
public import Lemmata.FrankWolfePS.Upper.Joint
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-! On a norm-compact instance the trial-step recurrence is little-o of the inverse budget
when the limiting gradient uniquely exposes the minimizer. -/
@[expose] public section
namespace Lemmata.FrankWolfePS
open Filter Finset
open scoped Topology RealInnerProductSpace NNReal Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem compact_exposure {C : Set E} (hc : IsCompact C) {star g : E} (hs : star∈C)
    (hm : ∀ y∈C,⟪g,star⟫≤⟪g,y⟫) (hu : ∀ y∈C,⟪g,y⟫=⟪g,star⟫ → y=star)
    (x : ℕ → E) (mem : ∀ t,x t∈C) (tends : Tendsto (fun t => ⟪g,x t-star⟫) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 star) := by
  apply Metric.tendsto_nhds.mpr; intro ε ep
  let D := C ∩ {y | ε≤dist y star}
  have cd : IsCompact D := hc.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  by_cases ne : D.Nonempty
  · obtain ⟨m,hmD,least⟩ := cd.exists_isMinOn ne (show Continuous (fun z : E => ⟪g,z⟫) from continuous_const.inner continuous_id).continuousOn
    have pos : 0<⟪g,m-star⟫ := by
      rw [inner_sub_right,sub_pos]; apply lt_of_le_of_ne (hm m hmD.1)
      intro e; have eq := hu m hmD.1 e.symm
      have h : ε≤dist m star := hmD.2; rw [eq,dist_self] at h; linarith
    filter_upwards [tends.eventually_lt_const pos] with n hn
    by_contra! far; have H := isMinOn_iff.mp least (x n) ⟨mem n,far⟩
    rw [inner_sub_right,inner_sub_right] at hn; linarith
  · exact Eventually.of_forall (fun n => lt_of_not_ge (fun h => ne ⟨x n,mem n,h⟩))

private theorem cesaro_recurrence (h d : ℕ → ℝ) (L : ℝ) (lp : 0≤L)
    (hn : ∀ t,0≤h t) (dn : ∀ t,0≤d t) (lim : Tendsto d atTop (𝓝 0))
    (rec : ∀ t,h (t+1)≤(1-Upper.fwStepSize t)*h t + L/2*Upper.fwStepSize t^2*d t) :
    Tendsto (fun t : ℕ => (t:ℝ)*h t) atTop (𝓝 0) := by
  have tel (n : ℕ) : (n:ℝ)*((n:ℝ)+1)*h n ≤ 2*L*∑ i∈range n,d i := by
    induction n with
    | zero => simp
    | succ n ih =>
      have pos : 0<(n:ℝ)+2 := by positivity
      have e := mul_le_mul_of_nonneg_left (rec n) (by positivity : 0≤((n:ℝ)+1)*((n:ℝ)+2))
      simp only [Upper.fwStepSize] at e
      have c : ((n:ℝ)+1)*((n:ℝ)+2)*((1-2/((n:ℝ)+2))*h n+L/2*(2/((n:ℝ)+2))^2*d n)=
          n*((n:ℝ)+1)*h n+2*L*d n*((n:ℝ)+1)/((n:ℝ)+2) := by field_simp; ring
      rw [c] at e
      have cut : 2*L*d n*((n:ℝ)+1)/((n:ℝ)+2) ≤ 2*L*d n := by
        rw [div_le_iff₀ pos]; nlinarith only [mul_nonneg lp (dn n)]
      rw [sum_range_succ]; push_cast; nlinarith only [ih,e,cut]
  have avg := tendsto_const_nhds (x:=2*L) |>.mul lim.cesaro
  simp only [mul_zero] at avg
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (hn n))) _ avg
  filter_upwards [eventually_ge_atTop 1] with n pp
  have p : 0<(n:ℝ) := by exact_mod_cast pp
  rw [← mul_assoc,← div_eq_mul_inv,div_mul_eq_mul_div,le_div_iff₀ p]
  nlinarith only [tel n,mul_nonneg p.le (hn n)]

/-- Proposition 7.1 in its norm-compact Hilbert form. The hypothesis is the stated trial
inequality itself and allows every choice of exact linear minimizer along the trajectory. -/
theorem compact_trial_little_o [CompleteSpace E] {C : Set E} (hc : IsCompact C) (_hv : Convex ℝ C)
    {f : E → ℝ} {L : ℝ≥0} (hf : Differentiable ℝ f) (cv : ConvexOn ℝ Set.univ f)
    (lip : LipschitzWith L (gradient f)) {star : E} (hs : star∈C) (opt : IsMinOn f C star)
    (_nz : gradient f star≠0)
    (un : ∀ y∈C,IsMinOn (fun w => ⟪gradient f star,w⟫) C y ↔ y=star)
    (O : Upper.LMO C) (x : ℕ → E) (mem : ∀ t,x t∈C)
    (trial : ∀ t,let s := O.query (gradient f (x t))
      f (x (t+1)) ≤ f (x t)+Upper.fwStepSize t*⟪gradient f (x t),s-x t⟫+
        (L:ℝ)/2*Upper.fwStepSize t^2*‖s-x t‖^2) :
    Tendsto (fun t : ℕ => (t:ℝ)*(f (x t)-f star)) atTop (𝓝 0) := by
  let s := fun t => O.query (gradient f (x t))
  let h := fun t => f (x t)-f star
  let d := fun t => ‖s t-x t‖^2
  let D := Metric.diam C
  have hn (t) : 0≤h t := sub_nonneg.mpr (isMinOn_iff.mp opt _ (mem t))
  have lower (y z : E) : f y+⟪gradient f y,z-y⟫≤f z :=
    Lemmata.FrankWolfeLDS.isFirstOrderConvex_of_convexOn hf cv y z
  have mr := isMinOn_iff.mp ((un star hs).mpr rfl)
  have unique (y) (hy : y∈C) (eq : ⟪gradient f star,y⟫=⟪gradient f star,star⟫) : y=star :=
    (un y hy).mp (isMinOn_iff.mpr (fun z hz => eq ▸ mr z hz))
  have bound (y z : E) (hy : y∈C) (hz : z∈C) : ‖y-z‖≤D := by
    simpa [D,dist_eq_norm] using Metric.dist_le_diam_of_mem hc.isBounded hy hz
  have hrec (t) : h (t+1)≤(1-Upper.fwStepSize t)*h t + (L:ℝ)/2*Upper.fwStepSize t^2*d t := by
    have e := lower (x t) star
    have l := O.least (gradient f (x t)) star hs
    have g : ⟪gradient f (x t),s t-x t⟫ ≤ -h t := by
      rw [inner_sub_right] at e ⊢; dsimp [h,s]; linarith
    have a := mul_le_mul_of_nonneg_left g (Upper.stepSize_bounds t).1
    have b := trial t
    change f (x (t+1))≤f (x t)+_+(L:ℝ)/2*Upper.fwStepSize t^2*d t at b
    dsimp [h] at a ⊢; linarith
  have coarse := Upper.fw_rate_scalar h (C:=(L:ℝ)*D^2) (by positivity) (fun t => by
    have de := pow_le_pow_left₀ (norm_nonneg _) (bound (s t) (x t) (O.mem _) (mem t)) 2
    apply (hrec t).trans; rw [add_le_add_iff_left]
    change _*‖_ - _‖^2≤_
    nlinarith only [mul_le_mul_of_nonneg_left de (by positivity : 0≤(L:ℝ)/2*Upper.fwStepSize t^2)])
  have zero : Tendsto h atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    apply squeeze_zero (fun n => hn (n+1)) coarse
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let g := gradient f star
  have expose := compact_exposure hc hs mr unique
  have xx : Tendsto x atTop (𝓝 star) := by
    apply expose x mem
    apply squeeze_zero _ (fun t => by dsimp [h]; linarith [lower star (x t)]) zero
    intro t; rw [inner_sub_right]; exact sub_nonneg.mpr (mr _ (mem t))
  have gg := lip.continuous.continuousAt.tendsto.comp xx
  have ss : Tendsto s atTop (𝓝 star) := by
    apply expose s (fun _ => O.mem _)
    have lim : Tendsto (fun t => ‖g-gradient f (x t)‖*D) atTop (𝓝 0) := by
      simpa [g,Function.comp_def] using (((tendsto_const_nhds (x:=g)).sub gg).norm.mul_const D)
    apply squeeze_zero _ _ lim
    · intro t; rw [inner_sub_right]; exact sub_nonneg.mpr (mr _ (O.mem _))
    · intro t
      have a := O.least (gradient f (x t)) star hs
      have b := real_inner_le_norm (g-gradient f (x t)) (s t-star)
      rw [inner_sub_left,inner_sub_right (gradient f (x t))] at b
      have w := mul_le_mul_of_nonneg_left (bound (s t) star (O.mem _) hs) (norm_nonneg (g-gradient f (x t)))
      dsimp [s,g] at *; linarith
  have dd : Tendsto d atTop (𝓝 0) := by simpa [d] using (ss.sub xx).norm.pow 2
  exact cesaro_recurrence h d L (by positivity) hn (fun _ => _root_.sq_nonneg _) dd hrec
end Lemmata.FrankWolfePS
