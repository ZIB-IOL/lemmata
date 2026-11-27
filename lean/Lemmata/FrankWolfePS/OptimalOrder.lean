module
public import Lemmata.FrankWolfePS.Proofs
/-! Both sides of the finite optimal-order corollary for the same disclosed quadratic. -/
@[expose] public section
namespace Lemmata.FrankWolfePS
open MeasureTheory
variable {ι Ω : Type} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω]

/-- Corollary 3.5. The upper method works simultaneously for every body in the prescribed
class. For each randomized method there is a fixed body in that same class on which even
its unrestricted output fails with probability at least one fifth. -/
theorem optimal_order (T : ℕ) (T2 : 2≤T) (a : ι) (size : Fintype.card ι=256*(T+1))
    {L β D : ℝ} (hL : 0<L) (hb : 0<β) (hD : 2/β<D)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : Ω → Method (Ambient ι) T)
    (hm : Method.IsMeasurable m) :
    let st := Unique.hardStart β D a
    let f := hardObjective (ι:=ι) L (1/β)
    (∃ upper : Method (Ambient ι) T, ∀ C,PrescribedBody β D st C → ∀ O : Upper.LMO C,
      upper.run O.query∈C ∧ f (upper.run O.query)-sInf (f '' C)≤2*L*(D-2/β)^2/((T:ℝ)+1)) ∧
    ∃ C,PrescribedBody β D st C ∧ IsLMO C (uniqueLMO C st) ∧
      1/5≤μ.real {ω | (m ω).run (uniqueLMO C st)∉C ∨
        L*(D-2/β)^2/(64*((T:ℝ)+1))≤f ((m ω).run (uniqueLMO C st))-sInf (f '' C)} := by
  let st := Unique.hardStart β D a
  let f := hardObjective (ι:=ι) L (1/β)
  have hd := (div_lt_iff₀ hb).mp hD
  constructor
  · let e : Ambient ι := EuclideanSpace.single none (1:ℝ)
    have ep : e≠0 := by intro eq; have h := congrArg (fun x : Ambient ι => x none) eq; simpa [e] using h
    obtain ⟨upper,spec⟩ := quadratic_upper_bound_proof T T2 hL hb (hardCenter (1/β)) e ep
    refine ⟨upper,?_⟩; intro C hC O
    obtain ⟨hc,hv,_,diam,normals,_,stmem⟩ := hC
    have dia := (rolling_ball_proof hc hv ⟨st,stmem⟩ hb normals).2.2
    have dlow : 2/β≤Metric.diam C := by rw [dia,show 2/β=2*(1/β) by ring]; exact le_add_of_nonneg_right Metric.diam_nonneg
    obtain ⟨feas,gap⟩ := spec C hc hv normals dlow O
    obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn ⟨st,stmem⟩ (hardObjective_continuous L (1/β)).continuousOn
    have eq : sInf (f '' C)=f z := (IsLeast.csInf_eq ⟨⟨z,hz,rfl⟩,fun _ ⟨y,hy,ey⟩ => ey ▸ isMinOn_iff.mp hmin y hy⟩)
    have pp := gap z hz
    dsimp [Upper.iso] at pp
    rw [eq]; refine ⟨feas,?_⟩
    dsimp only [f]; rw [hardObjective_eq,hardObjective_eq]
    have up := pow_le_pow_left₀ (sub_nonneg.mpr dlow) (sub_le_sub_right diam (2/β)) 2
    have scale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left up (by positivity : 0≤2*L))
      (by positivity : 0≤(T:ℝ)+1)
    linarith
  · exact lower_bound_unique_lmo_proof T a size hL hb (by nlinarith) μ m hm
end Lemmata.FrankWolfePS
