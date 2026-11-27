module
public import Lemmata.FrankWolfePS.RandomHilbert.Coordinates
public import Lemmata.FrankWolfePS.RandomHilbert.Rate
public import Lemmata.FrankWolfePS.RandomHilbert.Probability
public import Lemmata.FrankWolfePS.RandomHilbert.Value
public import Lemmata.FrankWolfePS.RandomHilbert.Support
/-! Randomized fixed-Hilbert lower bounds with unique replies to every nonzero query. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open MeasureTheory Filter
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

def failures (M : Rules Ω) (T : ℕ) : Set (Tape × Ω) :=
  {p | let d := data p.1
       let w := output M T d p.2
       w∉body d ∨ rate T≤cost w-sInf (cost '' body d)}

theorem failures_measurable (M : Rules Ω) (T : ℕ) : MeasurableSet (failures M T) := by
  let D := fun p : Tape × Ω => data p.1
  let w := fun p : Tape × Ω => output M T (D p) p.2
  have md : Measurable D := data_meas.comp measurable_fst
  have mw : Measurable w := (output_measurable M T).comp (md.prodMk measurable_snd)
  have c : Continuous cost := by unfold cost; fun_prop
  have e : failures M T = {p | squaredDistance (D p) (w p)≠0} ∪
      {p | rate T≤cost (w p)-sInf (cost '' body (D p))} := by
    ext p; exact or_congr (not_congr (member_as_zero _ _)) Iff.rfl
  rw [e]; apply MeasurableSet.union
  · exact (measurableSet_eq_fun (squaredDistance_measurable.comp (md.prodMk mw)) measurable_const).compl
  · exact measurableSet_le measurable_const ((c.measurable.comp mw).sub (minimum_measurable.comp md))

theorem random_horizon (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Rules Ω) (T : ℕ) :
    (6/25:ℝ≥0∞)≤(prior.prod μ) (failures M T) := by
  let j := scale T
  let E := evidence M j T
  have m : MeasurableSet E := evidence_meas _ _ _
  have low (ω : Ω) : (6/25:ℝ≥0∞)≤prior ((fun x => (x,ω)) ⁻¹' E) :=
    lower_resample marginal j (measurable_prodMk_right m) _ (fun x => conditional_bound M ω x j T (scale_fits T))
  have joint : (6/25:ℝ≥0∞)≤(prior.prod μ) E := by
    rw [Measure.prod_apply_symm m]
    simpa using (lintegral_mono (μ:=μ) (f:=fun _ => (6/25:ℝ≥0∞)) low)
  apply joint.trans; apply measure_mono; rintro ⟨x,ω⟩ hx
  let d := data x
  obtain ⟨u,hu⟩ := exists_minimal d
  have bad := distant_gap hu j (data_card x j) hx
  change output M T d ω∉body d ∨ rate T≤cost (output M T d ω)-sInf (cost '' body d)
  exact bad.imp_right (fun h => by rw [←(value_eq hu).2]; exact (rate_le_scale T).trans h)

/-- Bounded-depth methods may return immediately or after any of at most T calls.
Only their actual query and output rules on finite histories must be jointly measurable. -/
theorem random_bounded (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (m : Ω → Method World T)
    (ha : Unique.BorelRule (fun ω h => (m ω).queryAfter h.reverse))
    (ho : Unique.BorelRule (fun ω h => (m ω).outAfter h.reverse)) :
    (6/25:ℝ≥0∞)≤(prior.prod μ) {p : Tape × Ω | let d := data p.1
      let w := (m p.2).run (oracle d)
      w∉body d ∨ rate T≤cost w-sInf (cost '' body d)} := by
  let M : Rules Ω := ⟨fun ω h => (m ω).queryAfter h.reverse,fun ω h => (m ω).outAfter h.reverse,ha,ho⟩
  have h := random_horizon μ M T
  simpa only [failures,output,M,Method.outAfter_play _ _ (le_refl T)] using h

theorem random_anytime (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Rules Ω) :
    ∃ x : Tape, (∀ n,∃ T≥n,(1/5:ℝ≥0∞)≤μ ((Prod.mk x) ⁻¹' failures M T)) ∧
      (1/5:ℝ≥0∞)≤μ {ω | ∀ n,∃ T≥n,(x,ω)∈failures M T} := by
  obtain ⟨x,h,k⟩ := fixed_parameter prior μ (fun j => failures M (budget j))
    (fun j => failures_measurable M (budget j)) (fun j => random_horizon μ M (budget j))
  have time (j) : j≤budget j := by
    have e : j<2^j := Nat.lt_two_pow_self
    change j≤2^j-1; omega
  refine ⟨x,fun n => ?_,k.trans (measure_mono ?_)⟩
  · obtain ⟨j,hj,b⟩ := h n; exact ⟨budget j,hj.trans (time j),b⟩
  · intro ω he n; obtain ⟨j,hj,z⟩ := he n; exact ⟨budget j,hj.trans (time j),z⟩

/-- The geometric and probabilistic conclusions use one explicitly defined prior.
Its support is witnessed in the Hausdorff distance on nonempty closed bounded sets. -/
theorem randomized_fixed_hilbert :
    (∀ x : Tape,let d := data x
      IsCompact (toWeakSpace ℝ World '' body d) ∧ Convex ℝ (body d) ∧
      Upper.LipschitzNormals (body d) 1 ∧ Metric.diam (body d)≤15/4 ∧ publicStart∈body d ∧
      oracle d 0=publicStart ∧ (∀ q,Unique.MinAt (body d) q (oracle d q)) ∧
      (∀ q : World,q≠0 → ∃! z,Unique.MinAt (body d) q z) ∧
      (∀ ε : ℝ,0<ε → ∃ E : Set Tape,MeasurableSet E ∧ 0<prior E ∧
        ∀ y∈E,Metric.hausdorffDist (body d) (body (data y))<ε)) ∧
    (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Rules Ω) (T : ℕ),
      (1/5:ℝ≥0∞)≤(prior.prod μ) (failures M T)) ∧
    (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Rules Ω),
      ∃ x : Tape, (∀ n,∃ T≥n,(1/5:ℝ≥0∞)≤μ ((Prod.mk x) ⁻¹' failures M T)) ∧
      (1/5:ℝ≥0∞)≤μ {ω | ∀ n,∃ T≥n,(x,ω)∈failures M T}) := by
  refine ⟨fun x => ?_,fun μ _ M T => ?_,fun μ _ M => random_anytime μ M⟩
  · let d := data x
    exact ⟨weak_compact d,body_convex d,body_normals d,
      Metric.diam_le_of_forall_dist_le (by norm_num) (fun _ hx _ hy => by simpa only [dist_eq_norm] using width hx hy),
      public_mem d,oracle_zero d,oracle_spec d,fun _ h => oracle_unique d h,fun _ h => hausdorff_support x h⟩
  · have f : (1/5:ℝ≥0∞)≤6/25 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    exact f.trans (random_horizon μ M T)
end Lemmata.FrankWolfePS.RandomHilbert
