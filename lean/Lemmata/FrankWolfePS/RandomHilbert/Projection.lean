module
public import Lemmata.FrankWolfePS.RandomHilbert.Geometry
/-! The true optimizer is close to the hidden barycenter in every block. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset Filter
open scoped RealInnerProductSpace Topology BigOperators
noncomputable def size {d : Data} (u : Param d) := ‖ctr u-target‖
noncomputable def residual {d : Data} (u : Param d) := size u-rad u
noncomputable def theta {d : Data} (u : Param d) := 1-rad u/size u
noncomputable def closest {d : Data} (u : Param d) := target+theta u • (ctr u-target)
theorem size_sq {d : Data} (u : Param d) : size u^2=1089+‖horizontal u‖^2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (ctr u-target)
  change _=‖(1:ℝ)-(-32)‖^2+‖horizontal u-0‖^2 at h
  norm_num [size] at h ⊢; exact h
theorem size_bounds {d : Data} (u : Param d) : 33≤size u ∧ size u≤34 := by
  have nn : 0≤size u := norm_nonneg _
  constructor <;> nlinarith [size_sq u,horizontal_bound u,norm_nonneg (horizontal u),
    _root_.sq_nonneg ‖horizontal u‖,mul_self_le_mul_self (norm_nonneg (horizontal u)) (horizontal_bound u)]
theorem theta_bounds {d : Data} (u : Param d) : 969/1000≤theta u ∧ theta u≤1 := by
  have sz := size_bounds u
  have sr := rad_bounds u
  have sp : 0<size u := by linarith
  have h : rad u/size u ≤ 31/1000 := (div_le_iff₀ sp).mpr (by linarith)
  have p := div_nonneg (show 0≤rad u by linarith) sp.le
  unfold theta; constructor <;> linarith
theorem exists_minimal (d : Data) : ∃ u : Param d, ∀ v : Param d,residual u≤residual v := by
  have c : Continuous (residual (d:=d)) := ((ctr_cont d).sub continuous_const).norm.sub (rad_cont d)
  let : Nonempty (Param d) := ⟨seedPar d⟩
  obtain ⟨u,_,hm⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α:=Param d)) c.continuousOn
  exact ⟨u,fun v => isMinOn_iff.mp hm v (Set.mem_univ _)⟩

theorem closest_spec {d : Data} {u : Param d} (best : ∀ v : Param d,residual u≤residual v) :
    closest u∈body d ∧ IsMinOn (fun z => ‖z-target‖) (body d) (closest u) := by
  have sp : 0<size u := by linarith [(size_bounds u).1]
  have rp : 0≤rad u := by linarith [(rad_bounds u).1]
  have tp : 0≤theta u := by linarith [(theta_bounds u).1]
  have e : closest u-ctr u= -(rad u/size u) • (ctr u-target) := by
    unfold closest theta; rw [sub_smul,one_smul,neg_smul]; abel
  refine ⟨⟨u,?_⟩,isMinOn_iff.mpr ?_⟩
  · rw [e,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (div_nonneg rp sp.le)]
    change rad u/size u*size u≤rad u; rw [div_mul_cancel₀ _ sp.ne']
  · rintro y ⟨v,hv⟩
    have eu : ‖closest u-target‖=residual u := by
      unfold closest; rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg tp]
      change (1-rad u/size u)*size u=size u-rad u
      rw [sub_mul,one_mul,div_mul_cancel₀ _ sp.ne']
    have t := norm_add_le (ctr v-y) (y-target)
    rw [sub_add_sub_cancel,norm_sub_rev (ctr v) y] at t
    change size v≤_ at t; rw [eu]; have b := best v; unfold residual at b ⊢; linarith

theorem change_one {f g : ℕ → ℝ} (sf : Summable f) (sg : Summable g) (j : ℕ)
    (eq : ∀ i,i≠j → f i=g i) : (∑' i,f i)-(∑' i,g i)=f j-g j := by
  rw [← sf.tsum_sub sg,tsum_eq_single j]; intro i hi; simp [eq i hi]

private theorem bary_difference {ι : Type*} [Fintype ι] [DecidableEq ι] {I : Finset ι}
    (ne : I.Nonempty) {u : ι → ℝ} (hu : Base I u) :
    ‖liftVec u-liftVec (simplexBarycenter I)‖^2=‖liftVec u‖^2-‖liftVec (simplexBarycenter I)‖^2 := by
  let v := simplexBarycenter I
  have eq : ⟪liftVec u,liftVec v⟫=‖liftVec v‖^2 := by
    rw [lift_inner,lift_sq,bary_sq ne]; change (∑ i,u i*(if i∈I then 1/(I.card:ℝ) else 0))=_
    simp only [mul_ite,mul_zero,sum_ite_mem,univ_inter,← sum_mul,hu.2.2,one_mul]
  rw [norm_sub_sq_real,eq]; ring

theorem opt_block {d : Data} {u : Param d} (best : ∀ v : Param d,residual u≤residual v) (j : ℕ)
    (card : (allowed (d j)).card=8*K j) :
    Real.sqrt (K j:ℝ)*‖theta u • liftVec (u j).val-liftVec (simplexBarycenter (allowed (d j)))‖≤1/64 := by
  let I := allowed (d j)
  have ne : I.Nonempty := insert_nonempty _ _
  let v := simplexBarycenter I
  let w := Function.update u j (⟨v,barycenter_base ne⟩ : {z // Base (allowed (d j)) z})
  have diff := change_one (sq_blocks_sm (horizontal u)) (sq_blocks_sm (horizontal w)) j
    (fun i hi => by simp [w,Function.update_of_ne hi])
  rw [← norm_sq_sum,← norm_sq_sum] at diff
  simp only [horizontal_apply,w,Function.update_self,norm_smul,Real.norm_eq_abs,abs_of_pos (amp_pos _),mul_pow,amp_sq] at diff
  have rb := change_one (bonus_sm u) (bonus_sm w) j (fun i hi => by simp [w,Function.update_of_ne hi])
  have near : rad u-rad w≤2*eta j := by
    unfold rad
    linarith [(bonus_bound (D:=(d j).1) (u j).property).2,(bonus_bound (D:=(d j).1) (w j).property).1]
  let n := ‖liftVec (u j).val-liftVec v‖
  have normid : n^2=‖liftVec (u j).val‖^2-‖liftVec v‖^2 := bary_difference ne (u j).property
  have id : size u^2-size w^2=energy j*n^2 := by rw [normid,mul_sub,size_sq,size_sq]; change ‖horizontal u‖^2-‖horizontal w‖^2=_ at diff; linarith only [diff]
  have b := best w
  change size u-rad u≤size w-rad w at b
  have order : size w≤size u := by
    have nn := mul_nonneg (energy_pos j).le (_root_.sq_nonneg n)
    nlinarith [id,(size_bounds u).1,(size_bounds w).1]
  have energyBound : energy j*n^2 ≤ 136*eta j := by
    have both : size u+size w≤68 := by linarith [(size_bounds u).2,(size_bounds w).2]
    have z := mul_le_mul (show size u-size w≤2*eta j by linarith) both
      (by linarith [(size_bounds u).1,(size_bounds w).1]) (mul_nonneg (by norm_num) (eta_pos j).le)
    nlinarith only [z,id]
  have kp : 0<(K j:ℝ) := by exact_mod_cast K_pos j
  have en := energy_pos j
  have smallN : (K j:ℝ)*n^2 ≤ 136/10000000 := by
    unfold eta at energyBound
    rw [mul_div_assoc',le_div_iff₀ (by positivity)] at energyBound
    apply le_of_mul_le_mul_left (a:=energy j) _ en
    nlinarith only [energyBound]
  let k := Real.sqrt (K j:ℝ)
  have k2 : k^2=K j := Real.sq_sqrt kp.le
  have k0 : 0≤k := Real.sqrt_nonneg _
  have nsmall : k*n ≤ 4/1000 := by
    have sq : (k*n)^2≤136/10000000 := by rw [mul_pow,k2]; exact smallN
    nlinarith only [sq,_root_.sq_nonneg (k*n-4/1000)]
  have bn : (k*‖liftVec v‖)^2=1/8 := by
    rw [mul_pow,k2,lift_sq,bary_sq ne]; change (K j:ℝ)*(1/((allowed (d j)).card:ℝ))=_
    rw [card]; push_cast; field_simp
  have bs : k*‖liftVec v‖≤36/100 := by nlinarith only [bn,_root_.sq_nonneg (k*‖liftVec v‖-36/100)]
  have t := theta_bounds u
  have th : 0≤theta u := by linarith
  have eq : theta u • liftVec (u j).val-liftVec v =
      theta u • (liftVec (u j).val-liftVec v)-(1-theta u) • liftVec v := by simp only [smul_sub,sub_smul,one_smul]; abel
  rw [eq]
  have bound := norm_sub_le (theta u • (liftVec (u j).val-liftVec v)) ((1-theta u) • liftVec v)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg th,abs_of_nonneg (sub_nonneg.mpr t.2)] at bound
  change _≤theta u*n+(1-theta u)*‖liftVec v‖ at bound
  have h1 := mul_le_mul_of_nonneg_right t.2 (mul_nonneg k0 (norm_nonneg (liftVec (u j).val-liftVec v)))
  have h2 := mul_le_mul (show 1-theta u≤31/1000 by linarith) bs (mul_nonneg k0 (norm_nonneg _)) (by norm_num)
  change k*_≤_
  nlinarith only [mul_le_mul_of_nonneg_left bound k0,h1,h2,nsmall]

theorem projection_gap {d : Data} {u : Param d} (best : ∀ v : Param d,residual u≤residual v)
    {y : World} (hy : y∈body d) : ‖y-closest u‖^2/2≤cost y-cost (closest u) := by
  have cl := closest_spec best
  let C := body d
  let z := closest u
  let g : C → ℝ := fun w => ‖target-w.val‖
  have lo (w : C) : ‖target-z‖≤g w := by
    change ‖target-z‖≤‖target-w.val‖
    simpa only [norm_sub_rev target] using isMinOn_iff.mp cl.2 w.val w.property
  have bb : BddBelow (Set.range g) := ⟨0,Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩
  let : Nonempty C := ⟨⟨z,cl.1⟩⟩
  have inf : ‖target-z‖=⨅ w : C,‖target-w.val‖ := le_antisymm (le_ciInf lo) (ciInf_le bb ⟨z,cl.1⟩)
  have vi := (norm_eq_iInf_iff_real_inner_le_zero (body_convex d) cl.1).mp inf y hy
  have e : ‖y-target‖^2=‖y-z‖^2+‖target-z‖^2-2*⟪target-z,y-z⟫ := by
    rw [show y-target=(y-z)-(target-z) by abel,norm_sub_sq_real,real_inner_comm (target-z) (y-z)]; ring
  rw [norm_sub_rev target z] at e; change _≤‖y-target‖^2/2-‖z-target‖^2/2; linarith

noncomputable def extract (j : ℕ) (y : World) : Block j := (amp j)⁻¹ • y.snd j
def distant (j : ℕ) (J : Finset (Label j)) (y : World) :=
  1/(128*(K j:ℝ))≤‖extract j y-liftVec (simplexBarycenter (insert 0 J))‖^2
theorem distant_gap {d : Data} {u : Param d} (best : ∀ v : Param d,residual u≤residual v) (j : ℕ)
    (card : (allowed (d j)).card=8*K j) {y : World} (far : distant j (d j).2 y) :
    y∉body d ∨ energy j/(400*(K j:ℝ))≤cost y-cost (closest u) := by
  by_cases hy : y∈body d
  · right
    let k := Real.sqrt (K j:ℝ)
    let z := closest u
    let v := liftVec (simplexBarycenter (allowed (d j)))
    let m := theta u • liftVec (u j).val
    have a := amp_pos j
    have kp : 0<(K j:ℝ) := by exact_mod_cast K_pos j
    have ks : k^2=K j := Real.sq_sqrt kp.le
    have kl : 0≤k := Real.sqrt_nonneg _
    have zd : z.snd j=amp j • m := by
      change (0:Block j)+theta u • (amp j • liftVec (u j).val-0)=_
      simp [m,smul_smul,mul_comm]
    have yd : y.snd j=amp j • extract j y := by simp [extract,smul_smul,a.ne']
    have block := lp.norm_apply_le_norm (p:=2) (by norm_num) (y-z).snd j
    have world := WithLp.norm_snd_le (p:=2) (x:=y-z)
    change ‖y.snd j-z.snd j‖≤_ at block
    rw [zd,yd,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos a] at block
    have low : (7:ℝ)/80≤k*‖extract j y-v‖ := by
      change _≤‖extract j y-v‖^2 at far
      rw [div_le_iff₀ (by positivity)] at far
      have sq : 1/128≤(k*‖extract j y-v‖)^2 := by rw [mul_pow,ks]; linarith
      nlinarith only [sq,mul_nonneg kl (norm_nonneg (extract j y-v))]
    have loc : k*‖m-v‖≤1/64 := opt_block best j card
    have tri := norm_add_le (extract j y-m) (m-v)
    rw [sub_add_sub_cancel] at tri
    have lower : 7/80-1/64≤k*‖extract j y-m‖ := by linarith [mul_le_mul_of_nonneg_left tri kl]
    have p1 := mul_le_mul_of_nonneg_left lower a.le
    have p2 := mul_le_mul_of_nonneg_left (block.trans world) kl
    have b : amp j*(7/80-1/64) ≤ k*‖y-z‖ := by linarith
    have s := pow_le_pow_left₀ (mul_nonneg a.le (by norm_num : (0:ℝ)≤7/80-1/64)) b 2
    rw [mul_pow,mul_pow,amp_sq,ks] at s
    have pg := projection_gap best hy
    apply le_trans _ pg; rw [div_le_iff₀ (by positivity)]
    change _≤‖y-z‖^2/2*_
    nlinarith only [s,energy_pos j]
  · exact Or.inl hy
end Lemmata.FrankWolfePS.RandomHilbert
