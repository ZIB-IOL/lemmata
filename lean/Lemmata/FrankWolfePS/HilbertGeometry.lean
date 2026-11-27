module
public import Lemmata.FrankWolfePS.HilbertSeed
public import Lemmata.FrankWolfePS.Upper.FW

/-! Convexity, curvature, width and the matching open-loop rate for the same fixed body. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped Topology RealInnerProductSpace BigOperators

private theorem mix_center {u v : ℕ → ℝ} (hu : u∈simplex) (hv : v∈simplex) (a b : ℝ) :
    center (fun i => a*u i+b*v i) = a • center u+b • center v := by
  have lin (x : ℕ → ℝ) (hx : x∈simplex) : Summable (fun i => (weight i)^2*x i) := by
    simpa using null_terms_summable (show Tendsto (fun i => (weight i)^2) atTop (𝓝 0) by
      simpa using weight_limit.pow 2) (tendsto_const_nhds (x:=(0:ℝ))) hx
  have ea := (((lin u hu).hasSum.mul_left a).add ((lin v hv).hasSum.mul_left b)).tsum_eq
  have ex := (((synth_summable hu).hasSum.const_smul a).add ((synth_summable hv).hasSum.const_smul b)).tsum_eq
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (∑' i, (weight i)^2*(a*u i+b*v i)) = a*height u+b*height v
    unfold height
    convert ea using 2; ext i; ring
  · change (∑' i, (a*u i+b*v i) • axis i) = a • synth u+b • synth v
    simpa only [synth,add_smul,smul_smul] using ex

private theorem mix_radius {u v : ℕ → ℝ} (hu : u∈simplex) (hv : v∈simplex)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    a*radius u+b*radius v ≤ radius (fun i => a*u i+b*v i) := by
  have e := score_concave (penalty_limit 1) (penalty_limit 1) (fun i => by unfold penalty; positivity)
    hu hv ha hb hab
  unfold radius
  linarith

theorem fixed_convex : Convex ℝ fixedBody := by
  rintro y ⟨u,hu,du⟩ z ⟨v,hv,dv⟩ a b ha hb hab
  refine ⟨_,simplex_mix hu hv ha hb hab,?_⟩
  rw [mix_center hu hv,show a • y+b • z-(a • center u+b • center v)=a • (y-center u)+b • (z-center v) by
    simp only [smul_sub]; abel]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
  exact (add_le_add (mul_le_mul_of_nonneg_left du ha) (mul_le_mul_of_nonneg_left dv hb)).trans (mix_radius hu hv ha hb hab)

def fixedCore : Set Ambient := ballUnion center (fun u => radius u-1)

theorem fixed_rounded : fixedBody=Rounded fixedCore 1 :=
  ballUnion_rounded center radius (fun _ hu => (radius_bounds hu).1)

theorem fixed_normals {z w n m : Ambient} (hz : z∈fixedBody) (hw : w∈fixedBody)
    (hn : ‖n‖=1) (hm : ‖m‖=1) (hs : Supports fixedBody z n) (ht : Supports fixedBody w m) :
    ‖n-m‖ ≤ ‖z-w‖ := by
  rw [fixed_rounded] at hz hw hs ht
  simpa using rounded_lipschitz_normals (by norm_num : (0:ℝ)<1) hz hw hn hm hs ht

private theorem inner_synth_axis_lower {u : ℕ → ℝ} (hu : u∈simplex) (j : ℕ) :
    -(1/64:ℝ) ≤ ⟪axis j,synth u⟫ := by
  have e := (synth_summable hu).hasSum.mapL (innerSL ℝ (axis j))
  have lf (i) : -(1/64:ℝ)*u i ≤ (innerSL ℝ (axis j)) (u i • axis i) := by
    change _≤⟪axis j,u i • axis i⟫
    rw [real_inner_smul_right,axis_inner,mul_comm]
    apply mul_le_mul_of_nonneg_left _ (hu.1 i)
    unfold entry
    split <;> linarith [weight_small (max j i)]
  have low := ((mass_summable hu).mul_left (-(1/64:ℝ))).tsum_le_tsum lf e.summable
  rw [tsum_mul_left,e.tsum_eq] at low
  change -(1/64:ℝ)*(∑' i,u i) ≤ ⟪axis j,synth u⟫ at low
  linarith [mass_le_one hu]

theorem center_width {u v : ℕ → ℝ} (hu : u∈simplex) (hv : v∈simplex) : ‖center u-center v‖ ≤ 3/2 := by
  have e := (synth_summable hv).hasSum.mapL (innerSL ℝ (synth u))
  have lf (i) : -(1/64:ℝ)*v i ≤ (innerSL ℝ (synth u)) (v i • axis i) := by
    change _ ≤ ⟪synth u,v i • axis i⟫
    rw [real_inner_smul_right,real_inner_comm (axis i) (synth u),mul_comm]
    exact mul_le_mul_of_nonneg_left (inner_synth_axis_lower hu i) (hv.1 i)
  have low := ((mass_summable hv).mul_left (-(1/64:ℝ))).tsum_le_tsum lf e.summable
  rw [tsum_mul_left,e.tsum_eq] at low
  change -(1/64:ℝ)*(∑' i,v i) ≤ ⟪synth u,synth v⟫ at low
  have h := WithLp.prod_norm_sq_eq_of_L2 (center u-center v)
  change ‖center u-center v‖^2=‖height u-height v‖^2+‖synth u-synth v‖^2 at h
  rw [Real.norm_eq_abs,sq_abs,norm_sub_sq_real (synth u) (synth v)] at h
  have w₁ : ‖synth u‖^2≤1 := by nlinarith [norm_synth_le hu,norm_nonneg (synth u)]
  have w₂ : ‖synth v‖^2≤1 := by nlinarith [norm_synth_le hv,norm_nonneg (synth v)]
  have a := height_bounds hu
  have b := height_bounds hv
  have d : |height u-height v|≤1/4 := abs_le.mpr ⟨by linarith,by linarith⟩
  nlinarith [sq_abs (height u-height v),mul_nonneg (show 0≤1/4-|height u-height v| by linarith)
    (show 0≤1/4+|height u-height v| by positivity), mass_le_one hv]

theorem fixed_width {z y : Ambient} (hz : z∈fixedBody) (hy : y∈fixedBody) : ‖z-y‖ ≤ 15/4 := by
  obtain ⟨u,hu,du⟩ := hz
  obtain ⟨v,hv,dv⟩ := hy
  have h := norm_add_le (z-center u) (center u-center v)
  have j := norm_add_le (z-center v) (center v-y)
  rw [sub_add_sub_cancel] at h j
  rw [norm_sub_rev (center v) y] at j
  linarith [center_width hu hv,(radius_bounds hu).2,(radius_bounds hv).2,(height_bounds hu).2,(height_bounds hv).2]


private theorem quad_identity (x y : Ambient) :
    objective y = objective x+⟪grad x,y-x⟫+‖y-x‖^2/2 := by
  have e : grad y=grad x+(y-x) := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change y.fst+4=x.fst+4+(y.fst-x.fst); ring
    · change y.snd=x.snd+(y.snd-x.snd); abel
  unfold objective; rw [e,norm_add_sq_real]; ring

theorem fixed_models : Upper.Models fixedBody objective grad 1 where
  lower x _ y _ := by linarith [quad_identity x y,_root_.sq_nonneg ‖y-x‖]
  upper x _ y _ := by linarith [quad_identity x y]

/-- The actual LMO on this body is total, including at the zero direction. -/
theorem fixed_lmo_exists : Nonempty (Upper.LMO fixedBody) := by
  classical
  have e (q : Ambient) : ∃ z, z∈fixedBody ∧ IsMinOn (fun v => ⟪q,v⟫) fixedBody z := by
    by_cases h : q=0
    · subst q; exact ⟨seed,seed_mem,isMinOn_iff.mpr (by simp)⟩
    · have hn := (fixed_unique_oracle (-q) (neg_ne_zero.mpr h)).exists
      simpa only [isMaxOn_iff,isMinOn_iff,inner_neg_left,neg_le_neg_iff] using hn
  exact ⟨⟨fun q => (e q).choose,fun q => (e q).choose_spec.1,fun q => isMinOn_iff.mp (e q).choose_spec.2⟩⟩

/-- On one body and one exposed seed, open-loop Frank–Wolfe has matching upper and lower
bounds at every positive iteration, for any total exact LMO. -/
theorem fixed_open_loop_rate (O : Upper.LMO fixedBody) (n : ℕ) :
    let z := (Upper.fwRun grad O.query (fun _ => 1) seed (n+1)).1
    31/(256*((n:ℝ)+2)) ≤ objective z-objective optimum ∧
    objective z-objective optimum ≤ 2*((15:ℝ)/4)^2/((n:ℝ)+3) := by
  let q := fun j => (Upper.fwRun grad O.query (fun _ => 1) seed j).1
  let s := fun j => O.query (grad (q j))
  have mem (j : ℕ) : q j∈convexHull ℝ (insert seed (s '' Set.Iio j)) := by
    induction j with
    | zero => exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    | succ j ih =>
      let hull := convexHull ℝ (insert seed (s '' Set.Iio (j+1)))
      have old : q j∈hull := convexHull_mono (Set.insert_subset_insert (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ j)))) ih
      have new' : s j∈hull := subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨j,Nat.lt_succ_self j,rfl⟩)
      exact Upper.blend_mem (convex_convexHull ℝ _) (Upper.stepSize_bounds j).1 (Upper.stepSize_bounds j).2 old new'
  have low := fixed_gradient_lower q s mem (fun j => ⟨O.mem _,isMinOn_iff.mpr (O.least _)⟩) (n+1) (mem _)
  have up := Upper.fw_rate fixed_convex fixed_models (by norm_num) (fun _ hx _ hy => fixed_width hx hy)
    O (fun _ => 1) seed_mem optimum_mem n
  constructor
  · convert low using 1; push_cast; ring
  · simpa using up


/-- Any hull method whose next query is at least as good as the open-loop segment trial
has the same two-sided rate. Exact line search and full correction admit that trial;
for this quadratic the clipped short-step model is the objective on the segment. -/
theorem fixed_trial_rate (O : Upper.LMO fixedBody) (q : ℕ → Ambient)
    (hull : ∀ t,q t∈convexHull ℝ (insert seed ((fun j => O.query (grad (q j))) '' Set.Iio t)))
    (trial : ∀ t,objective (q (t+1)) ≤ objective (Upper.blend (Upper.fwStepSize t) (q t) (O.query (grad (q t)))))
    (n : ℕ) : 31/(256*((n:ℝ)+2)) ≤ objective (q (n+1))-objective optimum ∧
      objective (q (n+1))-objective optimum ≤ 2*((15:ℝ)/4)^2/((n:ℝ)+3) := by
  have mem (t) : q t∈fixedBody := by
    apply convexHull_min _ fixed_convex (hull t)
    rintro _ (rfl|⟨j,_,rfl⟩)
    · exact seed_mem
    · exact O.mem _
  have low := fixed_gradient_lower q (fun j => O.query (grad (q j))) hull
    (fun j => ⟨O.mem _,isMinOn_iff.mpr (O.least _)⟩) (n+1) (hull _)
  refine ⟨by convert low using 1; push_cast; ring,?_⟩
  apply Upper.fw_rate_scalar (fun t => objective (q t)-objective optimum) (by positivity)
  intro j
  have h := Upper.fw_one_step fixed_convex fixed_models (by norm_num) (fun _ hx _ hy => fixed_width hx hy) O
    (mem j) optimum_mem (Upper.stepSize_bounds j).1 (Upper.stepSize_bounds j).2
  linarith [trial j]

end Lemmata.FrankWolfePS.Hilbert
