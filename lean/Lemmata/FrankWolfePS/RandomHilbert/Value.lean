module
public import Lemmata.FrankWolfePS.RandomHilbert.Prior
public import Mathlib.Analysis.LocallyConvex.WeakSpace
/-! Joint Borel measurability of body membership and the actual minimum.
The existing dimension-free Frank–Wolfe estimate approximates squared distance to
each sampled body by jointly measurable finite oracle computations. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
theorem body_closed (d : Data) : IsClosed (body d) := by
  have h := (weak_compact d).isClosed.preimage (toWeakSpaceCLM ℝ World).continuous
  change IsClosed ((toWeakSpace ℝ World) ⁻¹' ((toWeakSpace ℝ World) '' body d)) at h
  rwa [Set.preimage_image_eq _ (toWeakSpace ℝ World).injective] at h

noncomputable def squaredDistance (d : Data) (z : World) := Metric.infDist z (body d)^2/2
private noncomputable def finitePoint (d : Data) (z : World) (n : ℕ) :=
  (Upper.fwRun (fun x => x-z) (oracle d) (fun _ => 1) publicStart n).1
private theorem point_meas (n : ℕ) : Measurable (fun p : Data × World => finitePoint p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have mo := oracle_measurable.comp (measurable_fst.prodMk (ih.sub measurable_snd))
    exact ((measurable_const (a:=1-Upper.fwStepSize n)).smul ih).add
      ((measurable_const (a:=Upper.fwStepSize n)).smul mo)
private theorem point_limit (d : Data) (z : World) :
    Tendsto (fun n => ‖finitePoint d z (n+1)-z‖^2/2) atTop (𝓝 (squaredDistance d z)) := by
  let O : Upper.LMO (body d) := ⟨oracle d,fun q => (oracle_spec d q).1,fun q => (oracle_spec d q).2⟩
  have model : Upper.Models (body d) (fun x => ‖x-z‖^2/2) (fun x => x-z) 1 := by
    constructor <;> intro x _ y _
    all_goals
      have h := Upper.iso_taylor 1 z x y
      simp only [Upper.iso,Upper.isoGrad,one_smul] at h
      linarith [_root_.sq_nonneg ‖y-x‖]
  obtain ⟨v,hv,eq⟩ := exists_norm_eq_iInf_of_complete_convex ⟨publicStart,public_mem d⟩
    (body_closed d).isComplete (body_convex d) z
  have distv : Metric.infDist z (body d)=‖v-z‖ := by
    calc Metric.infDist z (body d) = ⨅ w : body d,‖z-w.val‖ := by simp only [Metric.infDist_eq_iInf,dist_eq_norm]
         _ = ‖z-v‖ := eq.symm
         _ = ‖v-z‖ := norm_sub_rev _ _
  have lower n : squaredDistance d z≤‖finitePoint d z (n+1)-z‖^2/2 := by
    have m := Upper.fwRun_mem (body_convex d) O (fun x => x-z) (fun _ => 1) (public_mem d) (n+1)
    have q := Metric.infDist_le_dist_of_mem (x:=z) m
    rw [dist_eq_norm,norm_sub_rev z] at q
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ Metric.infDist_nonneg q 2) (by norm_num)
  let c : ℝ := 2*((15:ℝ)/4)^2
  have up n : ‖finitePoint d z (n+1)-z‖^2/2≤squaredDistance d z+c/((n:ℝ)+3) := by
    have bound := Upper.fw_rate (body_convex d) model (by norm_num) (fun _ hx _ hy => width hx hy)
      O (fun _ => 1) (public_mem d) hv n
    unfold squaredDistance; rw [distv]; change ‖finitePoint d z (n+1)-z‖^2/2-‖v-z‖^2/2≤2*(1*(15/4)^2)/((n:ℝ)+3) at bound
    dsimp [c]; linarith only [bound]
  have lim := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 3)
  have lim' : Tendsto (fun n : ℕ => c/((n:ℝ)+3)) atTop (𝓝 0) := by simpa [Function.comp_def] using lim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds (x:=squaredDistance d z)).add lim') lower up

theorem squaredDistance_measurable : Measurable (fun p : Data × World => squaredDistance p.1 p.2) := by
  apply measurable_of_tendsto_metrizable (f:=fun n (p : Data × World) => ‖finitePoint p.1 p.2 (n+1)-p.2‖^2/2)
  · intro n; exact (((point_meas (n+1)).sub measurable_snd).norm.pow_const 2).div_const _
  · exact tendsto_pi_nhds.mpr (fun p => point_limit p.1 p.2)
theorem member_as_zero (d : Data) (z : World) : z∈body d ↔ squaredDistance d z=0 := by
  rw [(body_closed d).mem_iff_infDist_zero ⟨publicStart,public_mem d⟩]
  simp [squaredDistance]
theorem value_eq {d : Data} {u : Param d} (best : ∀ v : Param d,residual u≤residual v) :
    squaredDistance d target=cost (closest u) ∧ cost (closest u)=sInf (cost '' body d) := by
  let w := closest u
  have m := closest_spec best
  have eq : Metric.infDist target (body d)=‖w-target‖ := by
    apply le_antisymm
    · rw [norm_sub_rev w target,←dist_eq_norm]; exact (show Metric.infDist target (body d)≤dist target w from Metric.infDist_le_dist_of_mem m.1)
    · rw [Metric.infDist_eq_iInf]; let : Nonempty (body d) := ⟨⟨w,m.1⟩⟩
      apply le_ciInf; intro x; rw [dist_eq_norm,norm_sub_rev target]
      exact isMinOn_iff.mp m.2 x.val x.property
  refine ⟨by simp [squaredDistance,cost,eq,w],?_⟩
  apply Eq.symm; apply IsLeast.csInf_eq
  refine ⟨⟨_,m.1,rfl⟩,?_⟩; rintro _ ⟨x,hx,rfl⟩
  linarith [projection_gap best hx,_root_.sq_nonneg ‖x-closest u‖]
theorem minimum_eq (d : Data) : sInf (cost '' body d)=squaredDistance d target := by
  obtain ⟨u,hu⟩ := exists_minimal d
  have h := value_eq (d:=d) (u:=u) hu
  exact (h.1.trans h.2).symm
theorem minimum_measurable : Measurable (fun d : Data => sInf (cost '' body d)) := by
  simp_rw [minimum_eq]
  have m : Measurable (fun d : Data => (d,target)) := measurable_prodMk_right
  exact fun s hs => m (squaredDistance_measurable hs)
end Lemmata.FrankWolfePS.RandomHilbert
