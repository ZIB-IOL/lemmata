module
public import Lemmata.FrankWolfePS.RandomHilbert.Model
/-! Compact parameter maps, convexity, width and inner unit balls of the physical set. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Filter Finset
open scoped Topology BigOperators RealInnerProductSpace
theorem rad_cont (d : Data) : Continuous (rad (d:=d)) := by
  apply continuous_const.add
  refine continuous_tsum (f:=fun j (u : Param d) => bonus (d j).1 (u j).val) (u:=fun j => energy j/1000) ?_ (sum_energy.div_const 1000) ?_
  · intro j
    have t : Continuous (bonus (d j).1) := by unfold bonus linear sq; fun_prop
    exact t.comp (continuous_subtype_val.comp (continuous_apply j))
  · intro j u
    rw [Real.norm_eq_abs,abs_of_nonneg (bonus_bound (u j).property).1]
    exact (bonus_bound (u j).property).2.trans (eta_le j)
theorem horizontal_cont (d : Data) : Continuous (horizontal (d:=d)) := by
  apply continuous_iff_continuousAt.mpr; intro v
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have cb (j) : Continuous (fun u : Param d => horizontal u j) := by
    change Continuous (fun u : Param d => amp j • WithLp.toLp 2 (u j).val)
    have ev : Continuous (fun u : Param d => (u j).val) :=
      continuous_subtype_val.comp (continuous_apply j)
    exact (continuous_const (y:=amp j)).smul ((PiLp.continuous_toLp 2 (fun _ : Label j => ℝ)).comp ev)
  have cc : Continuous (fun u : Param d => ∑' j,‖horizontal u j-horizontal v j‖^2) := by
    apply continuous_tsum (u:=fun j => 4*energy j) (fun j => ((cb j).sub continuous_const).norm.pow 2)
      (sum_energy.mul_left 4)
    intro j u
    have h (z : Param d) : ‖horizontal z j‖≤amp j := by
      rw [horizontal_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (amp_pos _)]
      exact mul_le_of_le_one_right (amp_pos _).le (lift_norm (z j).property)
    have diff := norm_sub_le (horizontal u j) (horizontal v j)
    rw [Real.norm_eq_abs,abs_of_nonneg (_root_.sq_nonneg _)]
    have q := pow_le_pow_left₀ (norm_nonneg _) (show ‖horizontal u j-horizontal v j‖≤2*amp j by linarith [h u,h v]) 2
    change ‖horizontal u j-horizontal v j‖^2≤4*energy j
    nlinarith only [q,amp_sq j]
  have eq (u : Param d) : dist (horizontal u) (horizontal v)=Real.sqrt (∑' j,‖horizontal u j-horizontal v j‖^2) := by
    rw [dist_eq_norm]; change ‖horizontal u-horizontal v‖=Real.sqrt (∑' j,‖(horizontal u-horizontal v) j‖^2)
    rw [←norm_sq_sum,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [eq]
  simpa [Function.comp_def] using ((Real.continuous_sqrt.comp cc).continuousAt (x:=v)).tendsto
theorem ctr_cont (d : Data) : Continuous (ctr (d:=d)) :=
  (WithLp.prod_continuous_toLp 2 ℝ Horiz).comp (continuous_const.prodMk (horizontal_cont d))

private noncomputable def combine {d : Data} (u v : Param d) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (sum : a+b=1) :
    Param d := fun j => ⟨Unique.mix a b (u j).val (v j).val,Unique.mix_base (u j).property (v j).property ha hb sum⟩
private theorem combine_ctr {d : Data} (u v : Param d) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (sum : a+b=1) :
    ctr (combine u v ha hb sum)=a • ctr u+b • ctr v := by
  apply WithLp.ofLp_injective; apply Prod.ext
  · change (1:ℝ)=a*1+b*1; linarith
  · change horizontal _=a • horizontal u + b • horizontal v
    ext j i; change amp j*(a*(u j).val i+b*(v j).val i)=a*(amp j*(u j).val i)+b*(amp j*(v j).val i);ring
private theorem combine_rad {d : Data} (u v : Param d) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (sum : a+b=1) :
    a*rad u+b*rad v≤rad (combine u v ha hb sum) := by
  let z := combine u v ha hb sum
  have comp (j) : a*bonus (d j).1 (u j).val+b*bonus (d j).1 (v j).val≤bonus (d j).1 (z j).val := by
    have lin : linear (noise 0 (spacing j) (d j).1) (z j).val =
        a*linear (noise 0 (spacing j) (d j).1) (u j).val+b*linear (noise 0 (spacing j) (d j).1) (v j).val := by
      unfold linear; rw [mul_sum,mul_sum,← sum_add_distrib]; apply sum_congr rfl
      intro i _; change _*(a*_+b*_) = _; ring
    have q := Unique.sq_mix (u j).val (v j).val sum
    change sq (z j).val=_ at q
    unfold bonus; rw [lin,q]
    nlinarith only [mul_nonneg (small j).1.le (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (fun i => (u j).val i-(v j).val i))),
      congrArg (fun x : ℝ => x*kappa j) sum]
  have h := ((bonus_sm u).mul_left a |>.add ((bonus_sm v).mul_left b)).tsum_le_tsum comp (bonus_sm z)
  rw [Summable.tsum_add ((bonus_sm u).mul_left a) ((bonus_sm v).mul_left b),tsum_mul_left,tsum_mul_left] at h
  change _≤rad z; unfold rad; linarith

theorem body_convex (d : Data) : Convex ℝ (body d) := by
  rintro x ⟨u,du⟩ y ⟨v,dv⟩ a b ha hb sum
  refine ⟨combine u v ha hb sum,?_⟩
  rw [combine_ctr,show a • x+b • y-(a • ctr u+b • ctr v)=a • (x-ctr u)+b • (y-ctr v) by simp only [smul_sub]; abel]
  have h := norm_add_le (a • (x-ctr u)) (b • (y-ctr v))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at h
  exact h.trans ((add_le_add (mul_le_mul_of_nonneg_left du ha) (mul_le_mul_of_nonneg_left dv hb)).trans (combine_rad u v ha hb sum))

theorem width {d : Data} {x y : World} (hx : x∈body d) (hy : y∈body d) : ‖x-y‖≤15/4 := by
  obtain ⟨u,hu⟩ := hx; obtain ⟨v,hv⟩ := hy
  have c : ctr u-ctr v=WithLp.toLp 2 ((0:ℝ),horizontal u-horizontal v) := by
    apply WithLp.ofLp_injective; apply Prod.ext
    · change (1:ℝ)-1=0; ring
    · rfl
  have h := norm_sub_le (horizontal u) (horizontal v)
  have t := norm_add_le (x-ctr u) (ctr u-ctr v)
  have b := norm_add_le (x-ctr v) (ctr v-y)
  rw [sub_add_sub_cancel,c,WithLp.norm_toLp_snd] at t
  rw [sub_add_sub_cancel,norm_sub_rev (ctr v) y] at b
  linarith [(rad_bounds u).2,(rad_bounds v).2,horizontal_bound u,horizontal_bound v]

theorem body_rounded (d : Data) : body d=Rounded {k | ∃ u : Param d, ‖k-ctr u‖≤rad u-1} 1 := by
  ext x; constructor
  · rintro ⟨u,hu⟩
    let c := fun _ : ℕ→ℝ => ctr u
    let r := fun _ : ℕ→ℝ => rad u
    have mem : x∈Hilbert.ballUnion c r := ⟨0,Hilbert.simplex_zero,hu⟩
    rw [Hilbert.ballUnion_rounded c r (fun _ _ => (rad_bounds u).1)] at mem
    obtain ⟨k,⟨v,hv,hk⟩,hx⟩ := mem
    exact ⟨k,⟨u,hk⟩,hx⟩
  · rintro ⟨k,⟨u,hu⟩,hx⟩; refine ⟨u,?_⟩
    have t := norm_add_le (x-k) (k-ctr u); rw [sub_add_sub_cancel] at t; linarith
theorem body_normals (d : Data) : Upper.LipschitzNormals (body d) 1 := by
  rw [body_rounded]; intro x hx y hy n m hn hm h g
  simpa using rounded_lipschitz_normals (by norm_num : (0:ℝ)<1) hx hy hn hm h g

theorem weak_compact (d : Data) : IsCompact (toWeakSpace ℝ World '' body d) := by
  let B : Set World := {x | ‖x‖≤1}
  let W := WeakSpace ℝ World
  let e := toWeakSpace ℝ World
  have c : IsCompact (e '' B) := by
    have z := Hilbert.ballUnion_weakly_compact (E:=World) (fun _ => 0) (fun _ => 1)
      (fun _ _ => le_rfl) continuous_const continuous_const
    have be : B=Hilbert.ballUnion (fun _ => (0:World)) (fun _ => 1) := by
      ext x; constructor
      · intro h; exact ⟨0,Hilbert.simplex_zero,by simpa [B] using h⟩
      · rintro ⟨u,hu,hx⟩; simpa [B] using hx
    rw [be]; exact z
  let F : Param d × W → W := fun p => e (ctr p.1)+rad p.1 • p.2
  have hF : Continuous F :=
    ((WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ World).flip (fun l =>
      l.continuous.comp (ctr_cont d))).comp continuous_fst).add (((rad_cont d).comp continuous_fst).smul continuous_snd)
  have eq : e '' body d=F '' ((Set.univ : Set (Param d)) ×ˢ (e '' B)) := by
    ext w; constructor
    · rintro ⟨x,⟨u,hu⟩,rfl⟩
      let v := (rad u)⁻¹ • (x-ctr u)
      have pos : 0<rad u := by linarith [(rad_bounds u).1]
      have mem : v∈B := by
        change ‖(rad u)⁻¹ • (x-ctr u)‖ ≤ 1
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos),inv_mul_le_iff₀ pos, mul_one]; exact hu
      refine ⟨(u,e v),⟨Set.mem_univ _,v,mem,rfl⟩,?_⟩
      apply e.symm.injective; change ctr u + rad u • ((rad u)⁻¹ • (x-ctr u))=x
      simp [smul_smul,pos.ne']
    · rintro ⟨⟨u,y⟩,⟨_,v,hv,rfl⟩,rfl⟩
      refine ⟨ctr u+rad u • v,⟨u,?_⟩,rfl⟩
      have pos : 0≤rad u := by linarith [(rad_bounds u).1]
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg pos]
      exact mul_le_of_le_one_right pos hv
  rw [eq]; exact (isCompact_univ.prod c).image hF
end Lemmata.FrankWolfePS.RandomHilbert
