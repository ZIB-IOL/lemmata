module
public import Lemmata.FrankWolfePS.Unique.Local
public import Lemmata.FrankWolfePS.Unique.Borel
public import Mathlib.Topology.Maps.Proper.Basic
/-! A finite simplex with a strictly convex quadratic penalty. Its unique selector
is continuous in the scores, and a separated label receives exactly zero weight. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset _root_.Lemmata.FrankWolfePS.Unique
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def linear (l u : ι → ℝ) := ∑ i,l i*u i
noncomputable def criterion (l : ι → ℝ) (s : ℝ) (u : ι → ℝ) := linear l u+s*sq u
omit [DecidableEq ι] in
theorem criterion_loss (l u : ι → ℝ) (s : ℝ) : criterion l s u=loss l s (1:ℝ) u := by
  simp [criterion,linear,loss,center,mul_comm]

noncomputable def arg (I : Finset ι) (l : ι → ℝ) (s : ℝ) : ι → ℝ := by
  classical exact if h : ∃ u, Base I u ∧ ∀ v,Base I v → criterion l s u ≤ criterion l s v then h.choose else 0

theorem arg_spec {I : Finset ι} (ne : I.Nonempty) (l : ι → ℝ) (s : ℝ) :
    Base I (arg I l s) ∧ ∀ v,Base I v → criterion l s (arg I l s) ≤ criterion l s v := by
  have co : Continuous (criterion l s) := by unfold criterion linear sq; fun_prop
  obtain ⟨u,hu,hm⟩ := (base_compact I).exists_isMinOn ⟨_,atom_base ne.choose_spec⟩ co.continuousOn
  have h : ∃ u,Base I u ∧ ∀ v,Base I v → criterion l s u ≤ criterion l s v :=
    ⟨u,hu,fun v hv => isMinOn_iff.mp hm v hv⟩
  simpa [arg,h] using h.choose_spec

theorem arg_eq {I : Finset ι} {l u : ι → ℝ} {s : ℝ} (hs : 0<s) (hu : Base I u)
    (hm : ∀ v,Base I v → criterion l s u ≤ criterion l s v) (ne : I.Nonempty) : u=arg I l s := by
  have h := arg_spec ne l s
  exact weights_unique (v:=l) (p:=(1:ℝ)) hs hu h.1
    (fun v hv => by simpa only [← criterion_loss] using hm v hv)
    (fun v hv => by simpa only [← criterion_loss] using h.2 v hv)

theorem arg_cont (I : Finset ι) (ne : I.Nonempty) {s : ℝ} (hs : 0<s) : Continuous (fun l => arg I l s) := by
  let V := {u : ι → ℝ | Base I u}
  let : CompactSpace V := isCompact_iff_compactSpace.mp (base_compact I)
  let F : (ι→ℝ) → V := fun l => ⟨arg I l s,(arg_spec ne l s).1⟩
  have graph : F.graph = ⋂ v : V,{p : (ι→ℝ) × V | criterion p.1 s p.2.val ≤ criterion p.1 s v.val} := by
    ext p; change (F p.1=p.2) ↔ _
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · rintro eq v; rw [← eq]; exact (arg_spec ne p.1 s).2 _ v.property
    · intro h; apply Subtype.ext; exact (arg_eq hs p.2.property (fun z hz => h ⟨z,hz⟩) ne).symm
  apply continuous_subtype_val.comp (continuous_of_isClosed_graph (f:=F) ?_)
  rw [graph]; apply isClosed_iInter; intro v
  let f : (ι→ℝ) × (ι→ℝ) → ℝ := fun p => criterion p.1 s p.2
  have c : Continuous f := by unfold f criterion linear sq; fun_prop
  exact isClosed_le (c.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (c.comp (continuous_fst.prodMk continuous_const))

theorem linear_eq_on {I : Finset ι} {l l' u : ι → ℝ} (hu : Base I u)
    (same : ∀ i∈I,l i=l' i) : linear l u=linear l' u := by
  apply sum_congr rfl; intro i _
  by_cases hi : i∈I
  · rw [same i hi]
  · simp [hu.2.1 i hi]

theorem arg_congr {I : Finset ι} (ne : I.Nonempty) {s : ℝ} (hs : 0<s)
    {l l' : ι → ℝ} (same : ∀ i∈I,l i=l' i) : arg I l s=arg I l' s := by
  have h := arg_spec ne l s
  apply arg_eq hs h.1 _ ne; intro v hv
  simpa only [criterion,← linear_eq_on h.1 same,← linear_eq_on hv same] using h.2 v hv

theorem arg_restrict {R I : Finset ι} (sub : R⊆I) {i : ι} (hi : i∈R) {s : ℝ}
    (hs : 0<s) {l : ι → ℝ} (sep : ∀ j∈I,j∉R → l i+2*s<l j) : arg I l s=arg R l s := by
  let u := arg I l s
  have h := arg_spec (⟨i,sub hi⟩ : I.Nonempty) l s
  have hz (j : ι) (hj : j∉R) : u j=0 := by
    by_cases mem : j∈I
    · exact excluded_weight (v:=l) (p:=(1:ℝ)) hs.le h.1
        (fun z hz => by simpa only [← criterion_loss] using h.2 z hz) mem (sub hi)
        (by simpa [Real.inner_apply] using sep j mem hj)
    · exact h.1.2.1 j mem
  apply arg_eq hs (base_restrict h.1 hz) _ ⟨i,hi⟩
  intro z hz'; exact h.2 z (base_restrict hz' (fun j hj => hz'.2.1 j (fun hj' => hj (sub hj'))))

omit [DecidableEq ι] in
theorem weighted_bound {I : Finset ι} {u l : ι → ℝ} (hu : Base I u) {e : ℝ}
    (h : ∀ i,0≤l i ∧ l i≤e) : 0≤linear l u ∧ linear l u≤e := by
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (h i).1 (hu.1 i)
  · have m := sum_le_sum (s:=(univ:Finset ι)) (fun i _ => mul_le_mul_of_nonneg_right (h i).2 (hu.1 i))
    simpa [linear,← mul_sum,base_total hu] using m

noncomputable def liftVec (u : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 u
omit [DecidableEq ι] in
theorem lift_sq (u : ι → ℝ) : ‖liftVec u‖^2=sq u := by
  simp [EuclideanSpace.real_norm_sq_eq,sq,liftVec]
theorem lift_norm {I : Finset ι} {u : ι → ℝ} (hu : Base I u) : ‖liftVec u‖≤1 := by
  nlinarith [lift_sq u,sq_base_le_one hu,norm_nonneg (liftVec u)]
omit [DecidableEq ι] in
theorem lift_inner (x : EuclideanSpace ℝ ι) (u : ι → ℝ) : ⟪x,liftVec u⟫=linear (fun i => x i) u := by
  simp [PiLp.inner_apply,linear,liftVec,mul_comm]

end Lemmata.FrankWolfePS.RandomHilbert
