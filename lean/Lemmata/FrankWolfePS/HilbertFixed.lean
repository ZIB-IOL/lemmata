module
public import Lemmata.FrankWolfePS.HilbertKernel
public import Lemmata.FrankWolfePS.HilbertBalls
public import Lemmata.FrankWolfePS.HilbertGradient
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The fixed gradient instance in an explicit Hilbert space. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped Topology RealInnerProductSpace BigOperators
abbrev Ambient := WithLp 2 (ℝ × Horizontal)
noncomputable def height (u : ℕ → ℝ) : ℝ := ∑' i, (weight i)^2 * u i
noncomputable def radius (u : ℕ → ℝ) : ℝ := 1 + score (penalty 1) (penalty 1) u
noncomputable def center (u : ℕ → ℝ) : Ambient := WithLp.toLp 2 (height u,synth u)
def fixedBody : Set Ambient := ballUnion center radius
noncomputable def dirLinear (q : Ambient) (i : ℕ) : ℝ :=
  q.fst*(weight i)^2 + ⟪q.snd,axis i⟫ + penalty ‖q‖ i
noncomputable def grad (z : Ambient) : Ambient := WithLp.toLp 2 (z.fst+4,z.snd)
noncomputable def objective (z : Ambient) : ℝ := ‖grad z‖^2/2
noncomputable def optimum : Ambient := WithLp.toLp 2 (-1,0)

private theorem hsum {u : ℕ → ℝ} (hu : u ∈ simplex) : Summable (fun i => (weight i)^2*u i) := by
  have h := null_terms_summable (show Tendsto (fun i => (weight i)^2) atTop (𝓝 0) by simpa using weight_limit.pow 2) (tendsto_const_nhds (x:=(0:ℝ))) hu
  simpa using h

private theorem rsum {u : ℕ → ℝ} (hu : u ∈ simplex) :
    Summable (fun i => penalty 1 i*u i - penalty 1 i*(u i)^2) :=
  null_terms_summable (penalty_limit 1) (penalty_limit 1) hu

theorem height_bounds {u : ℕ → ℝ} (hu : u ∈ simplex) : 0 ≤ height u ∧ height u ≤ 1/4096 := by
  refine ⟨tsum_nonneg (fun i => mul_nonneg (_root_.sq_nonneg _) (hu.1 i)), ?_⟩
  have le (i) : (weight i)^2*u i ≤ (1/4096)*u i := by
    apply mul_le_mul_of_nonneg_right _ (hu.1 i)
    nlinarith [sq_le_sq₀ (weight_pos i).le (by norm_num : (0:ℝ) ≤ 1/64) |>.mpr (weight_small i)]
  have h := (hsum hu).tsum_le_tsum le ((mass_summable hu).mul_left _)
  rw [tsum_mul_left] at h
  unfold height
  linarith [mass_le_one hu]

theorem radius_bounds {u : ℕ → ℝ} (hu : u ∈ simplex) : 1 ≤ radius u ∧ radius u ≤ 1+height u/100 := by
  have z (i) : 0 ≤ penalty 1 i *u i-penalty 1 i*(u i)^2 := by
    have hp : 0 ≤ penalty 1 i := by unfold penalty; positivity
    nlinarith [mul_nonneg hp (mul_nonneg (hu.1 i) (sub_nonneg.mpr (coord_le_one hu i)))]
  have le (i) : penalty 1 i*u i-penalty 1 i*(u i)^2 ≤ (1/100)*((weight i)^2*u i) := by
    unfold penalty
    nlinarith [mul_nonneg (_root_.sq_nonneg (weight i)) (_root_.sq_nonneg (u i))]
  have h := (rsum hu).tsum_le_tsum le ((hsum hu).mul_left _)
  rw [tsum_mul_left] at h
  unfold radius score height
  have pos : 0 ≤ ∑' i, (penalty 1 i * u i - penalty 1 i * (u i)^2) := tsum_nonneg z
  constructor <;> linarith

theorem dirLinear_limit (q : Ambient) : Tendsto (dirLinear q) atTop (𝓝 0) := by
  unfold dirLinear
  simpa using (((weight_limit.pow 2).const_mul q.fst).add (axis_null q.snd)).add (penalty_limit ‖q‖)

theorem fixed_value (q : Ambient) {u : ℕ → ℝ} (hu : u ∈ simplex) :
    ⟪q,center u⟫+‖q‖*radius u = ‖q‖+score (dirLinear q) (penalty ‖q‖) u := by
  have ha := (hsum hu).hasSum.mul_left q.fst
  have hb := (synth_summable hu).hasSum.mapL (innerSL ℝ q.snd)
  have hc := (rsum hu).hasSum.mul_left ‖q‖
  have hi : HasSum (fun i => dirLinear q i*u i-penalty ‖q‖ i*(u i)^2)
      (q.fst*height u+⟪q.snd,synth u⟫+‖q‖*score (penalty 1) (penalty 1) u) := by
    convert (ha.add hb).add hc using 1
    · ext i; simp [dirLinear,penalty]; ring
    · rfl
  rw [show score (dirLinear q) (penalty ‖q‖) u = _ from hi.tsum_eq]
  change ⟪q.fst,height u⟫+⟪q.snd,synth u⟫+‖q‖*(1+score (penalty 1) (penalty 1) u)=_
  rw [Real.inner_apply]
  ring

/-- The fixed body itself has exactly one supporting point in every nonzero Hilbert direction. -/
theorem fixed_unique_oracle (q : Ambient) (hq : q ≠ 0) :
    ∃! z, z ∈ fixedBody ∧ IsMaxOn (fun y => ⟪q,y⟫) fixedBody z :=
  unique_ball_oracle hq (fun _ hu => by linarith [(radius_bounds hu).1])
    (dirLinear_limit q) (penalty_limit ‖q‖) (fun i => by
      have h₀ := norm_pos_iff.mpr hq
      have h₁ := weight_pos i
      unfold penalty; positivity)
    (fun _ hu => fixed_value q hu)

/-- A box containing the entire body; the lower vertical face contains the minimizer. -/
theorem body_bounds {z : Ambient} (hz : z ∈ fixedBody) :
    -1 ≤ z.fst ∧ z.fst ≤ 2 ∧ ‖z.snd‖ ≤ 21/10 := by
  obtain ⟨u,hu,hd⟩ := hz
  have v := (WithLp.norm_fst_le (p:=2) (α:=ℝ) (β:=Horizontal) (x:=z-center u)).trans hd
  change |z.fst-height u| ≤ radius u at v
  have w := (WithLp.norm_snd_le (p:=2) (α:=ℝ) (β:=Horizontal) (x:=z-center u)).trans hd
  change ‖z.snd-synth u‖ ≤ radius u at w
  have lo := (abs_le.mp v).1
  have hi := (abs_le.mp v).2
  have hs := norm_sub_norm_le z.snd (synth u)
  have a := height_bounds hu
  have b := radius_bounds hu
  have h := norm_synth_le hu
  exact ⟨by linarith,by linarith,by linarith⟩

theorem optimum_mem : optimum ∈ fixedBody := by
  refine ⟨0,simplex_zero,?_⟩
  have hc : center 0=0 := by
    change WithLp.toLp 2 (height 0,synth 0) = WithLp.toLp 2 ((0:ℝ),(0:Horizontal))
    simp [height,synth]
  have hr : radius 0=1 := by simp [radius,score]
  rw [hc,sub_zero,hr]
  have e := WithLp.prod_norm_sq_eq_of_L2 optimum
  change ‖optimum‖^2=‖(-1:ℝ)‖^2+‖(0:Horizontal)‖^2 at e
  norm_num at e
  rcases e with e | e <;> linarith

theorem objective_gap {z : Ambient} (hz : -1 ≤ z.fst) :
    ‖z.snd‖^2/2 ≤ objective z-objective optimum := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (grad z)
  have hs := WithLp.prod_norm_sq_eq_of_L2 (grad optimum)
  change ‖grad z‖^2=‖z.fst+4‖^2+‖z.snd‖^2 at h
  change ‖grad optimum‖^2=‖(-1:ℝ)+4‖^2+‖(0:Horizontal)‖^2 at hs
  norm_num at hs
  rw [Real.norm_eq_abs,sq_abs] at h
  unfold objective
  nlinarith [_root_.sq_nonneg (z.fst+1)]

theorem optimum_min : IsMinOn objective fixedBody optimum :=
  isMinOn_iff.mpr (fun z hz => by linarith [objective_gap (body_bounds hz).1,_root_.sq_nonneg ‖z.snd‖])

end Lemmata.FrankWolfePS.Hilbert
