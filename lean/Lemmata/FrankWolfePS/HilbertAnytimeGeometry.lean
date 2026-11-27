module
public import Lemmata.FrankWolfePS.HilbertAnytimeMain
public import Lemmata.FrankWolfePS.HilbertWeak

/-! Weak compactness, width and the exact inner rolling radius of the arbitrary-query body. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.Hilbert.Anytime
open Lemmata.FrankWolfePS.Hilbert InnerProductSpace Finset Filter
open scoped Topology RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem frame_compact (F : Frame E) : IsCompact (toWeakSpace ℝ (World E) '' body F) := by
  have rc : Continuous (fun u : simplex => rad u) :=
    continuous_const.add (score_continuousOn bonus_limit (pen_limit 1)).domRestrict
  apply ballUnion_weakly_compact (ballCenter F) rad (fun _ h => rad_pos h) _ rc
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ (World E)).flip
  intro l
  let q := (toDual ℝ (World E)).symm l
  have hs := (score_continuousOn (lin_limit (orth_coeff_null F q.snd) ‖q‖) (pen_limit ‖q‖)).domRestrict
  have eq (u : simplex) : l (ballCenter F u)=q.fst+⟪q.snd,F.h⟫+‖q‖+
      score (lin (fun i => ⟪q.snd,F.e i⟫) ‖q‖) (pen ‖q‖) u-‖q‖*rad u := by
    rw [←toDual_symm_apply (x:=ballCenter F u) (y:=l)]
    linarith [frame_value F q u.property]
  change Continuous (fun u : simplex => l (ballCenter F u))
  simp only [eq]
  exact (continuous_const.add hs).sub (continuous_const.mul rc)

theorem frame_width (F : Frame E) {y z : World E} (hy : y∈body F) (hz : z∈body F) : ‖y-z‖ ≤ 15/4 := by
  obtain ⟨u,hu,du⟩ := hy
  obtain ⟨v,hv,dv⟩ := hz
  have sq (a : ℕ → ℝ) (ha : a∈simplex) : ‖reservoir F a‖^2≤1 := by
    rw [reservoir_sq F ha]
    exact ((ss ha).tsum_le_tsum (fun i => by nlinarith [mul_nonneg (ha.1 i) (sub_nonneg.mpr (coord_le_one ha i))])
      (mass_summable ha)).trans (mass_le_one ha)
  have e := ((reservoir_sm F hv).hasSum.mapL (innerSL ℝ (reservoir F u))).tsum_eq
  have nn : 0≤⟪reservoir F u,reservoir F v⟫ := by
    change 0≤(innerSL ℝ (reservoir F u)) (∑' i,v i • F.e i)
    rw [←e]
    apply tsum_nonneg
    intro i
    change 0≤⟪reservoir F u,v i • F.e i⟫
    rw [real_inner_smul_right,real_inner_comm (F.e i) (reservoir F u),reservoir_dot F hu]
    exact mul_nonneg (hv.1 i) (hu.1 i)
  have e := WithLp.prod_norm_sq_eq_of_L2 (ballCenter F u-ballCenter F v)
  change ‖ballCenter F u-ballCenter F v‖^2=‖(1:ℝ)-1‖^2+‖(F.h+reservoir F u)-(F.h+reservoir F v)‖^2 at e
  simp only [sub_self,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_sub_add_left_eq_sub,norm_sub_sq_real (reservoir F u) (reservoir F v)] at e
  have cw : ‖ballCenter F u-ballCenter F v‖≤3/2 := by nlinarith [sq u hu,sq v hv]
  have j := norm_add_le (y-ballCenter F u) (ballCenter F u-ballCenter F v)
  have k := norm_add_le (y-ballCenter F v) (ballCenter F v-z)
  rw [sub_add_sub_cancel] at j k
  rw [norm_sub_rev (ballCenter F v) z] at k
  linarith [rad_le hu,rad_le hv]

omit [CompleteSpace E] in
theorem frame_rounded (F : Frame E) : body F=Rounded (ballUnion (ballCenter F) (fun u => rad u-1)) 1 :=
  ballUnion_rounded _ _ (fun _ hu => rad_pos hu)

omit [CompleteSpace E] in
theorem frame_normals (F : Frame E) {z w n m : World E} (hz : z∈body F) (hw : w∈body F)
    (hn : ‖n‖=1) (hm : ‖m‖=1) (hs : Supports (body F) z n) (ht : Supports (body F) w m) :
    ‖n-m‖≤‖z-w‖ := by
  rw [frame_rounded F] at hz hw hs ht
  simpa using rounded_lipschitz_normals (by norm_num : (0:ℝ)<1) hz hw hn hm hs ht

private theorem bonus_mem : bonus∈simplex := ⟨fun i => (bonus_pos i).le,fun s => by linarith [bonus_sum s]⟩
private noncomputable def horizontalTilt (F : Frame E) : E := (-2:ℝ) • reservoir F bonus

omit [CompleteSpace E] in
private theorem tilt_small (F : Frame E) : ‖horizontalTilt F‖ < 1 := by
  have h : (∑' i,bonus i)≤1/256 := (mass_summable bonus_mem).tsum_le_of_sum_le bonus_sum
  have n : ‖reservoir F bonus‖≤∑' i,bonus i := by
    have hd (i) : ‖bonus i • F.e i‖=bonus i := by simp [norm_smul,abs_of_pos (bonus_pos i),F.orth.norm_eq_one]
    have sm : Summable (fun i => ‖bonus i • F.e i‖) := by simpa only [hd] using mass_summable bonus_mem
    simpa only [reservoir,hd] using norm_tsum_le_tsum_norm sm
  simp only [horizontalTilt,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

private theorem tilt_support (F : Frame E) (q : World E) (norm : ‖q‖=1) (tilt : q.snd=horizontalTilt F) :
    ballCenter F 0+q∈body F ∧ Supports (body F) (ballCenter F 0+q) q := by
  have hn : q≠0 := norm_ne_zero_iff.mp (by rw [norm]; norm_num)
  have val (i) : lin (fun j => ⟪q.snd,F.e j⟫) ‖q‖ i= -bonus i := by
    rw [lin,tilt,horizontalTilt,real_inner_smul_left,real_inner_comm (F.e i) (reservoir F bonus),reservoir_dot F bonus_mem,norm]; ring
  have r0 : rad 0=1 := by simp [rad,score]
  have tip0 : tip (ballCenter F 0) (rad 0) q=ballCenter F 0+q := by simp [tip,r0,unit,norm]
  refine ⟨tip0 ▸ tip_mem hn simplex_zero (by linarith [r0]),?_⟩
  rintro y ⟨u,hu,hy⟩
  have h := ball_value_le (q:=q) hy
  rw [frame_value F q hu] at h
  rw [←tip0,tip_value hn,frame_value F q simplex_zero]
  have sc : score (lin (fun j => ⟪q.snd,F.e j⟫) ‖q‖) (pen ‖q‖) u ≤ 0 := by
    apply tsum_nonpos; intro i
    rw [val,norm]
    have p : 0≤pen 1 i := by unfold pen; have := bonus_pos i; positivity
    nlinarith [mul_nonneg (bonus_pos i).le (hu.1 i),mul_nonneg p (_root_.sq_nonneg (u i))]
  simpa only [score,Pi.zero_apply,mul_zero,zero_pow (by decide : 2≠0),sub_zero,tsum_zero,add_zero]
    using h.trans (add_le_add_right sc _)

/-- A single supporting point and its unit normal obstruct every radius larger than one.
Together with the unit parallel-body identity this gives the exact maximum inner rolling radius. -/
theorem frame_radius_exact (F : Frame E) :
    ∃ z∈body F,∃ n : World E, ‖n‖=1 ∧ Supports (body F) z n ∧
      ∀ r : ℝ, 1<r → ∃ y : World E, ‖y-(z-r • n)‖≤r ∧ y∉body F := by
  let b := horizontalTilt F
  let a := Real.sqrt (1-‖b‖^2)
  have bp : 0<1-‖b‖^2 := by nlinarith [tilt_small F,norm_nonneg b]
  have ap : 0<a := Real.sqrt_pos.mpr bp
  have a2 : a^2=1-‖b‖^2 := Real.sq_sqrt bp.le
  let n : World E := WithLp.toLp 2 (a,b)
  let m : World E := WithLp.toLp 2 (-a,b)
  have un (q : World E) (v : ‖q.fst‖^2=a^2) (hi : q.snd=b) : ‖q‖=1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 q
    rw [v,hi] at h
    nlinarith [norm_nonneg q]
  have hn : ‖n‖=1 := un n (by change ‖a‖^2=a^2; simp) rfl
  have hm : ‖m‖=1 := un m (by change ‖-a‖^2=a^2; simp) rfl
  have dot : ⟪m,n⟫ < 1 := by
    change ⟪-a,a⟫+⟪b,b⟫<1
    rw [Real.inner_apply,real_inner_self_eq_norm_sq]; nlinarith [_root_.sq_pos_of_pos ap]
  have kn := tilt_support F n hn rfl
  have km := tilt_support F m hm rfl
  refine ⟨_,kn.1,n,hn,kn.2,?_⟩
  intro r hr
  let z := ballCenter F 0+n
  let y := (z-r • n)+r • m
  refine ⟨y,by change ‖(z-r • n)+r • m-(z-r • n)‖ ≤ r; simp [norm_smul,hm,abs_of_pos (show 0<r by linarith)],?_⟩
  intro inside
  have h := km.2 y inside
  simp only [y,z,inner_add_right,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hm] at h
  nlinarith [mul_pos (sub_pos.mpr hr) (sub_pos.mpr dot)]

end Lemmata.FrankWolfePS.Hilbert.Anytime
