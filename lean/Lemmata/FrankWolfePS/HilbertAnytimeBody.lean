module
public import Lemmata.FrankWolfePS.HilbertAnytime
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.Semicontinuity.Basic

/-! Geometric oracle and nearest-ball identities in the orthonormal frame of the amendment. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Lemmata.FrankWolfePS.Hilbert Finset Filter
open scoped Topology RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
abbrev World (E : Type*) := WithLp 2 (ℝ × E)
noncomputable def ballCenter (F : Frame E) (u : ℕ → ℝ) : World E :=
  WithLp.toLp 2 (1,F.h+reservoir F u)
def body (F : Frame E) : Set (World E) := ballUnion (ballCenter F) rad
noncomputable def target : World E := WithLp.toLp 2 (-32,0)

theorem rad_pos {u : ℕ → ℝ} (hu : u∈simplex) : 1≤rad u := by
  have pos (i) : 0≤bonus i*u i-pen 1 i*(u i)^2 := by
    unfold pen
    nlinarith [mul_nonneg (bonus_pos i).le (mul_nonneg (hu.1 i) (sub_nonneg.mpr (coord_le_one hu i))),
      mul_nonneg (bonus_pos i).le (hu.1 i)]
  have h : 0≤score bonus (pen 1) u := tsum_nonneg pos
  unfold rad; linarith

omit [CompleteSpace E] in
theorem orth_coeff_null (F : Frame E) (v : E) : Tendsto (fun i => ⟪v,F.e i⟫) atTop (𝓝 0) := by
  have lim := (F.orth.inner_products_summable v).tendsto_atTop_zero
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp lim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Function.comp_def,real_inner_comm v,Real.sqrt_sq_eq_abs] using h

theorem frame_value (F : Frame E) (q : World E) {u : ℕ → ℝ} (hu : u∈simplex) :
    ⟪q,ballCenter F u⟫+‖q‖*rad u = (q.fst+⟪q.snd,F.h⟫+‖q‖)+score (lin (fun i => ⟪q.snd,F.e i⟫) ‖q‖) (pen ‖q‖) u := by
  have hb := (reservoir_sm F hu).hasSum.mapL (innerSL ℝ q.snd)
  have hc := (null_terms_summable bonus_limit (pen_limit 1) hu).hasSum.mul_left ‖q‖
  have h : HasSum (fun i => lin (fun j => ⟪q.snd,F.e j⟫) ‖q‖ i*u i - pen ‖q‖ i*(u i)^2)
      (⟪q.snd,reservoir F u⟫+‖q‖*score bonus (pen 1) u) := by
    convert hb.add hc using 1
    · ext i; simp [lin,pen]; ring
    · rfl
  rw [show score _ _ u = _ from h.tsum_eq]
  change ⟪q.fst,(1:ℝ)⟫+⟪q.snd,F.h+reservoir F u⟫+‖q‖*(1+score bonus (pen 1) u)=_
  rw [Real.inner_apply,inner_add_right]; ring

/-- In every fixed frame, every nonzero physical direction has exactly one maximizing point. -/
theorem frame_unique_oracle (F : Frame E) (q : World E) (hq : q≠0) :
    ∃! z, z∈body F ∧ IsMaxOn (fun y => ⟪q,y⟫) (body F) z := by
  apply unique_ball_oracle hq (fun v hv => by linarith [(rad_pos hv)])
    (lin_limit (orth_coeff_null F q.snd) ‖q‖) (pen_limit ‖q‖) _ (fun v hv => frame_value F q hv)
  intro i; have := norm_pos_iff.mpr hq; have := bonus_pos i; unfold pen; positivity

theorem reservoir_dot (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) (i : ℕ) :
    ⟪F.e i,reservoir F u⟫=u i := by
  have e := ((reservoir_sm F hu).hasSum.mapL (innerSL ℝ (F.e i))).tsum_eq
  rw [tsum_eq_single i] at e
  · simpa [F.orth.norm_eq_one,reservoir] using e.symm
  · intro j hj
    simp [F.orth.inner_eq_zero (Ne.symm hj)]

theorem reservoir_h (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) : ⟪F.h,reservoir F u⟫=0 := by
  have e := ((reservoir_sm F hu).hasSum.mapL (innerSL ℝ F.h)).tsum_eq
  simpa [F.perp,reservoir] using e.symm

theorem reservoir_sq (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) : ‖reservoir F u‖^2=∑' i,(u i)^2 := by
  have e := ((reservoir_sm F hu).hasSum.mapL (innerSL ℝ (reservoir F u))).tsum_eq
  have h (i) : (innerSL ℝ (reservoir F u)) (u i • F.e i)=(u i)^2 := by
    change ⟪reservoir F u,u i • F.e i⟫=_
    rw [real_inner_smul_right,real_inner_comm (F.e i) (reservoir F u),reservoir_dot F hu,pow_two]
  rw [show ‖reservoir F u‖^2=⟪reservoir F u,reservoir F u⟫ from (real_inner_self_eq_norm_sq _).symm]
  rw [show (∑' i,(u i)^2) = _ from (tsum_congr h).symm,e]
  rfl

theorem center_distance (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) :
    ‖ballCenter F u-target‖=size u := by
  have e := WithLp.prod_norm_sq_eq_of_L2 (ballCenter F u-target)
  change ‖ballCenter F u-target‖^2=‖(1:ℝ)-(-32)‖^2+‖F.h+reservoir F u-0‖^2 at e
  rw [sub_zero,norm_add_sq_real,F.unit_h,reservoir_h F hu,reservoir_sq F hu] at e
  norm_num at e
  nlinarith [(size_bounds hu).2.2,(size_bounds hu).1,norm_nonneg (ballCenter F u-target)]

noncomputable def closest (F : Frame E) (u : ℕ → ℝ) : World E :=
  target+(1-rad u/size u) • (ballCenter F u-target)

/-- For every minimizing ball parameter, the constructed point is a global nearest point
of the full ball union to the disclosed quadratic center. -/
theorem closest_min (F : Frame E) {u : ℕ → ℝ} (hu : u∈simplex) (opt : IsMinOn residual simplex u) :
    closest F u∈body F ∧ IsMinOn (fun y => ‖y-target‖) (body F) (closest F u) := by
  have sp : 0<size u := by linarith [(size_bounds hu).1]
  have rp : 0≤rad u := by linarith [rad_pos hu]
  have th : 0≤1-rad u/size u := by linarith [theta_lower hu]
  have e : closest F u-ballCenter F u = -(rad u/size u) • (ballCenter F u-target) := by
    unfold closest
    rw [sub_smul,one_smul,neg_smul]; abel
  refine ⟨⟨u,hu,?_⟩,isMinOn_iff.mpr ?_⟩
  · rw [e,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (div_nonneg rp sp.le),center_distance F hu,div_mul_cancel₀ _ sp.ne']
  · rintro z ⟨v,hv,hd⟩
    have d : ‖closest F u-target‖=residual u := by
      unfold closest residual
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg th,center_distance F hu,sub_mul,
        div_mul_cancel₀ _ sp.ne',one_mul]
    have h := norm_add_le (ballCenter F v-z) (z-target)
    rw [sub_add_sub_cancel,norm_sub_rev (ballCenter F v) z,center_distance F hv] at h
    rw [d]; have m := isMinOn_iff.mp opt v hv
    unfold residual at m ⊢; linarith


/-- Lower semicontinuity of the distance term suffices for existence of a closest ball.
The norm-square need not be weakly continuous. -/
theorem exists_parameter : ∃ u∈simplex, IsMinOn residual simplex u := by
  let p := fun (n : ℕ) (u : simplex) => Real.sqrt (1090+∑ i ∈ range n, ((u:ℕ → ℝ) i)^2)-rad u
  have rc : Continuous (fun u : simplex => rad u) :=
    continuous_const.add (score_continuousOn bonus_limit (pen_limit 1)).domRestrict
  have cont (n : ℕ) : Continuous (p n) := by
    apply Continuous.sub _ rc
    apply Real.continuous_sqrt.comp
    apply Continuous.add continuous_const
    exact continuous_finsetSum _ (fun i _ => ((continuous_apply i).comp continuous_subtype_val).pow 2)
  have le (u : simplex) (n : ℕ) : p n u ≤ residual u := by
    apply sub_le_sub_right
    apply Real.sqrt_le_sqrt
    exact add_le_add_right ((ss u.property).sum_le_tsum _ (fun _ _ => _root_.sq_nonneg _)) _
  have eq (u : simplex) : (⨆ n,p n u)=residual u := by
    apply iSup_eq_of_forall_le_of_tendsto (F:=atTop) (le u)
    apply Filter.Tendsto.sub_const
    exact Real.continuous_sqrt.continuousAt.tendsto.comp (((ss u.property).hasSum.tendsto_sum_nat).const_add 1090)
  have lsc := lowerSemicontinuous_ciSup (f:=p) (fun u => ⟨residual u,Set.forall_mem_range.mpr (le u)⟩)
    (fun n => (cont n).lowerSemicontinuous)
  have : Nonempty simplex := ⟨⟨0,simplex_zero⟩⟩
  have : CompactSpace simplex := isCompact_iff_compactSpace.mp simplex_compact
  obtain ⟨u,_,best⟩ := LowerSemicontinuousOn.exists_isMinOn (Set.univ_nonempty (α:=simplex)) isCompact_univ (lsc.lowerSemicontinuousOn _)
  refine ⟨u,u.property,isMinOn_iff.mpr ?_⟩
  intro v hv
  simpa only [eq] using (isMinOn_iff.mp best ⟨v,hv⟩ (Set.mem_univ _))

theorem body_convex (F : Frame E) : Convex ℝ (body F) := by
  rintro y ⟨u,hu,du⟩ z ⟨v,hv,dv⟩ a b ha hb hab
  let w := fun i => a*u i+b*v i
  have hw : w∈simplex := simplex_mix hu hv ha hb hab
  have e := (((reservoir_sm F hu).hasSum.const_smul a).add ((reservoir_sm F hv).hasSum.const_smul b)).tsum_eq
  have ex : reservoir F w=a • reservoir F u+b • reservoir F v := by
    simpa only [w,reservoir,add_smul,smul_smul] using e
  have cm : ballCenter F w=a • ballCenter F u+b • ballCenter F v := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change (1:ℝ)=a*1+b*1; linarith
    · change F.h+reservoir F w=a • (F.h+reservoir F u)+b • (F.h+reservoir F v)
      rw [ex,smul_add,smul_add,show a • F.h+a • reservoir F u+(b • F.h+b • reservoir F v)=
        (a+b) • F.h+(a • reservoir F u+b • reservoir F v) by rw [add_smul]; abel,hab,one_smul]
  have sc := score_concave bonus_limit (pen_limit 1) (fun i => by have := bonus_pos i; unfold pen; positivity) hu hv ha hb hab
  have rc : a*rad u+b*rad v≤rad w := by dsimp [rad,w]; linarith
  refine ⟨w,hw,?_⟩
  rw [cm,show a • y+b • z-(a • ballCenter F u+b • ballCenter F v)=
    a • (y-ballCenter F u)+b • (z-ballCenter F v) by simp only [smul_sub]; abel]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
  exact (add_le_add (mul_le_mul_of_nonneg_left du ha) (mul_le_mul_of_nonneg_left dv hb)).trans rc

omit [CompleteSpace E] in
private theorem nearest_gap {C : Set E} (hc : Convex ℝ C) (p z : E) (hz : z∈C)
    (mn : IsMinOn (fun y => ‖y-p‖) C z) (y : E) (hy : y∈C) :
    ‖y-z‖^2/2 ≤ ‖y-p‖^2/2-‖z-p‖^2/2 := by
  let g : C → ℝ := fun w => ‖p-w.val‖
  let : Nonempty C := ⟨⟨z,hz⟩⟩
  have lo (w : C) : ‖p-z‖≤g w := by
    change ‖p-z‖≤‖p-w.val‖
    rw [norm_sub_rev p z,norm_sub_rev p w.val]
    exact isMinOn_iff.mp mn w.val w.property
  have bb : BddBelow (Set.range g) := ⟨0,Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩
  have up : (⨅ w : C,g w) ≤ g ⟨z,hz⟩ := ciInf_le bb ⟨z,hz⟩
  have inf : ‖p-z‖=⨅ w : C,‖p-w.val‖ := le_antisymm (le_ciInf lo) up
  have vi := (norm_eq_iInf_iff_real_inner_le_zero hc hz).mp inf y hy
  have eq : ‖y-p‖^2=‖y-z‖^2+‖p-z‖^2-2*⟪p-z,y-z⟫ := by
    rw [show y-p=(y-z)-(p-z) by abel,norm_sub_sq_real,real_inner_comm (p-z) (y-z)]; ring
  rw [norm_sub_rev p z] at eq
  linarith

/-- The geometric loss for any actual feasible output in the encoded finite span,
simultaneously for every budget and one body in the chosen frame. -/
theorem frame_all_budgets (F : Frame E) :
    ∃ z∈body F, IsMinOn (fun y => ‖y-target‖^2/2) (body F) z ∧
      ∀ (T : ℕ) (D : Set E), (∀ v∈D, ⟪witness F (T+1),v⟫=0) →
      ∀ y∈body F, y.snd∈Submodule.span ℝ ((fun i => F.h+F.e i) '' Set.Iio (T+1) ∪ D) →
      1/(4*((T:ℝ)+2)) ≤ ‖y-target‖^2/2-‖z-target‖^2/2 := by
  obtain ⟨u,hu,ho⟩ := exists_parameter
  let z := closest F u
  have hm := closest_min F hu ho
  refine ⟨z,hm.1,isMinOn_iff.mpr (fun y hy => ?_),?_⟩
  · have h := nearest_gap (body_convex F) target z hm.1 hm.2 y hy
    linarith [_root_.sq_nonneg ‖y-z‖]
  · intro T D hd y hy hyspan
    have small := span_gap F hu ho T D hd hyspan
    have comp := WithLp.norm_snd_le (p:=2) (α:=ℝ) (β:=E) (x:=z-y)
    change ‖(0+(1-rad u/size u) • (F.h+reservoir F u-0))-y.snd‖≤‖z-y‖ at comp
    simp only [sub_zero,zero_add] at comp
    have sq := pow_le_pow_left₀ (norm_nonneg _) comp 2
    rw [norm_sub_rev z y] at sq
    have h := nearest_gap (body_convex F) target z hm.1 hm.2 y hy
    linarith

end Lemmata.FrankWolfePS.Hilbert.Anytime
