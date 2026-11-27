module
public import Lemmata.FrankWolfePS.HilbertTrajectory

/-! The exposed initial atom, the one-call escape, and the failure of strong exposure. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert
open Finset Filter
open scoped Topology RealInnerProductSpace BigOperators

def delta (j i : ℕ) : ℝ := if i=j then 1 else 0
theorem delta_mem (j : ℕ) : delta j ∈ simplex := by
  refine ⟨fun i => by unfold delta; split <;> norm_num,fun s => ?_⟩
  simp [delta]; split <;> norm_num

theorem synth_delta (j : ℕ) : synth (delta j)=axis j := by
  unfold synth; rw [tsum_eq_single j]
  · simp [delta]
  · intro i hi; simp [delta,hi]

theorem height_delta (j : ℕ) : height (delta j)=(weight j)^2 := by
  unfold height; rw [tsum_eq_single j]
  · simp [delta]
  · intro i hi; simp [delta,hi]

theorem radius_delta (j : ℕ) : radius (delta j)=1 := by
  have h (i) : penalty 1 i*delta j i-penalty 1 i*(delta j i)^2=0 := by
    by_cases hi : i=j <;> simp [delta,hi]
  simp [radius,score,h]

noncomputable def seedDir : Ambient := WithLp.toLp 2 (-1,(1/8:ℝ) • axis 0)
noncomputable def seed : Ambient := tip (center (delta 0)) (radius (delta 0)) seedDir

private theorem seed_norm : 1≤‖seedDir‖ ∧ ‖seedDir‖≤2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 seedDir
  change ‖seedDir‖^2 = ‖(-1:ℝ)‖^2+‖(1/8:ℝ) • axis 0‖^2 at h
  rw [norm_smul] at h
  norm_num at h
  constructor <;> nlinarith [norm_nonneg seedDir, axis_norm_sq 0,weight_small 0,weight_pos 0]

theorem seed_mem : seed ∈ fixedBody :=
  tip_mem (norm_pos_iff.mp (by linarith [seed_norm.1])) (delta_mem 0)
    (by rw [radius_delta]; norm_num)

/-- The public seed is itself the uniquely exposed atom in the stated direction. -/
theorem seed_exposed : IsMaxOn (fun y => ⟪seedDir,y⟫) fixedBody seed := by
  have qp : 0<‖seedDir‖ := by linarith [seed_norm.1]
  have e := unique_parameter (dirLinear_limit seedDir) (penalty_limit ‖seedDir‖) (fun i => by
    have := weight_pos i; unfold penalty; positivity)
  obtain ⟨u,⟨hu,ho⟩,_⟩ := e
  have coeff (i) : dirLinear seedDir i = -(weight i)^2+(1/8)*entry 0 i+penalty ‖seedDir‖ i := by
    unfold dirLinear; change (-1:ℝ)*(weight i)^2+⟪(1/8:ℝ) • axis 0,axis i⟫+_ = _
    rw [real_inner_smul_left,axis_inner]; ring
  have sep : 0<dirLinear seedDir 0-2*penalty ‖seedDir‖ 0 := by
    rw [coeff]; norm_num [entry,penalty,weight]; linarith [seed_norm.2]
  have tail_nonpos (i : ℕ) (hi : 0 < i) : dirLinear seedDir i ≤ 0 := by
    rw [coeff]; simp only [entry,ite_eq_right (Nat.ne_of_lt hi),zero_sub,Nat.zero_max,penalty]
    nlinarith [mul_nonneg (show 0≤1-‖seedDir‖/100 by linarith [seed_norm.2]) (_root_.sq_nonneg (weight i)),
      weight_pos i]
  obtain ⟨tail,mass⟩ := maximizer_prefix hu
    (null_terms_summable (dirLinear_limit _) (penalty_limit _) hu) ho
    (fun i => by unfold penalty; positivity) sep (fun j hj => (tail_nonpos j hj).trans_lt sep)
  have ue : u=delta 0 := by
    funext i; cases i with
    | zero => simpa [delta] using mass
    | succ i => simp [delta,tail _ (Nat.zero_lt_succ _)]
  subst u
  apply isMaxOn_iff.mpr
  rintro z ⟨v,hv,hd⟩
  have h := (ball_value_le (q:=seedDir) hd)
  have cmp := isMaxOn_iff.mp ho v hv
  change ⟪seedDir,z⟫ ≤ ⟪seedDir,tip _ _ _⟫
  rw [tip_value (norm_pos_iff.mp qp),fixed_value _ (delta_mem 0)]
  rw [fixed_value _ hv] at h
  linarith

theorem seed_slice : seed ∈ physicalSlice 1 := by
  let m : ℝ := 1+‖seedDir‖⁻¹*(1/8)
  have z : 0 ≤ ‖seedDir‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have o : ‖seedDir‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ seed_norm.1
  let x := fun i => m*delta 0 i
  have hz (i : ℕ) (hi : 1 ≤ i) : x i=0 := by simp [x,delta,Nat.ne_of_gt hi]
  have mem : x ∈ prefixSlice 1 := by
    refine ⟨hz,?_⟩
    simp [x,delta,m]; constructor <;> linarith
  refine ⟨body_bounds seed_mem,x,mem,?_⟩
  rw [synth_finite hz]
  change synth (delta 0)+radius (delta 0) • (‖seedDir‖⁻¹ • ((1/8:ℝ) • axis 0)) = _
  simp [synth_delta,radius_delta,x,delta,m,add_smul,smul_smul]

/-- The fixed, uniquely exposed start and the true minimizing oracle give the budget bound
for every gradient-directed hull method, for all budgets on the same instance. -/
theorem fixed_gradient_lower (query reply : ℕ → Ambient)
    (hq : ∀ t, query t ∈ convexHull ℝ (insert seed (reply '' Set.Iio t)))
    (hr : ∀ t, reply t ∈ fixedBody ∧ IsMinOn (fun v => ⟪grad (query t),v⟫) fixedBody (reply t))
    (t : ℕ) {z : Ambient} (hz : z ∈ convexHull ℝ (insert seed (reply '' Set.Iio t))) :
    31 / (256 * ((t:ℝ)+1)) ≤ objective z-objective optimum :=
  fixed_hull_lower seed_slice query reply hq hr t hz

noncomputable def vertical : Ambient := WithLp.toLp 2 (1,0)
noncomputable def nearPoint (j : ℕ) : Ambient := WithLp.toLp 2 ((weight j)^2-1,axis j)

/-- One arbitrary query in the positive vertical direction returns the optimum. -/
theorem vertical_escape : ∃! y, y ∈ fixedBody ∧ IsMinOn (fun z => ⟪vertical,z⟫) fixedBody y := by
  have nz : -vertical ≠ 0 := by
    intro h; have e := congrArg (fun z : Ambient => z.fst) h; change -(1:ℝ)=0 at e; norm_num at e
  simpa only [isMinOn_iff,isMaxOn_iff,inner_neg_left,neg_le_neg_iff] using fixed_unique_oracle _ nz

theorem optimum_vertical : IsMinOn (fun z => ⟪vertical,z⟫) fixedBody optimum := by
  apply isMinOn_iff.mpr; intro z hz
  change ⟪(1:ℝ),-1⟫+⟪(0:Horizontal),0⟫ ≤ ⟪(1:ℝ),z.fst⟫+⟪(0:Horizontal),z.snd⟫
  simpa [Real.inner_apply] using (body_bounds hz).1

/-- Feasible near-maximizers of the negative vertical functional have vanishing deficit
and stay a fixed positive distance from its unique maximizer. -/
theorem failure_strong_exposure : (∀ j, nearPoint j∈fixedBody) ∧
    Tendsto (fun j => ⟪vertical,nearPoint j-optimum⟫) atTop (𝓝 0) ∧
    ∀ j, 9/10 ≤ ‖nearPoint j-optimum‖ := by
  refine ⟨fun j => ⟨delta j,delta_mem j,?_⟩,?_,?_⟩
  · rw [radius_delta]
    have e := WithLp.prod_norm_sq_eq_of_L2 (nearPoint j-center (delta j))
    change ‖_‖^2=‖(weight j)^2-1-height (delta j)‖^2+‖axis j-synth (delta j)‖^2 at e
    rw [height_delta,synth_delta] at e
    simpa using (show ‖nearPoint j-center (delta j)‖≤1 by
      simp at e; rcases e with e|e <;> linarith)
  · have h (j) : ⟪vertical, nearPoint j-optimum⟫=(weight j)^2 := by
      change ⟪(1:ℝ),(weight j)^2-1-(-1)⟫+⟪(0:Horizontal),axis j-0⟫=_
      simp
    simpa only [h,zero_pow (by decide : 2 ≠ 0)] using weight_limit.pow 2
  · intro j
    have h := WithLp.norm_snd_le (p:=2) (α:=ℝ) (β:=Horizontal) (x:=nearPoint j-optimum)
    change ‖axis j-0‖ ≤ _ at h
    simp only [sub_zero] at h
    nlinarith [axis_norm_sq j,weight_small j,norm_nonneg (axis j)]

end Lemmata.FrankWolfePS.Hilbert
