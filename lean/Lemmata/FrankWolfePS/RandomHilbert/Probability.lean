module
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic
/-! Product resampling and extraction of one parameter before the random seed. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open MeasureTheory Set Filter Finset
open scoped ENNReal BigOperators
variable {A : ℕ → Type*} [∀ i, MeasurableSpace (A i)]
/-- Replacing one coordinate of independent data by an independent copy preserves the law. -/
theorem resample (μ : ∀ j, Measure (A j)) [∀ j, IsProbabilityMeasure (μ j)] (j : ℕ) :
    ((Measure.infinitePi μ).prod (μ j)).map (fun p => Function.update p.1 j p.2) =
      Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply measurable_update' (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hj : j∈s
  · have e : (fun p : (∀ i,A i) × A j => Function.update p.1 j p.2) ⁻¹' (Set.pi (s : Set ℕ) t)
          = (Set.pi (↑(s.erase j) : Set ℕ) t) ×ˢ t j := by
      ext p; change (∀ i∈s,Function.update p.1 j p.2 i∈t i) ↔ (∀ i∈s.erase j,p.1 i∈t i) ∧ p.2∈t j
      constructor
      · intro h
        refine ⟨fun i hi => ?_,by simpa using h j hj⟩
        simpa [Function.update_of_ne (mem_erase.mp hi).1] using h i (mem_erase.mp hi).2
      · rintro ⟨a,b⟩ i hi
        by_cases e : i=j
        · subst i; simpa using b
        · simpa [Function.update_of_ne e] using a i (mem_erase.mpr ⟨e,hi⟩)
    rw [e,Measure.prod_prod,Measure.infinitePi_pi μ (fun i _ => ht i),←Finset.prod_erase_mul _ _ hj]
  · have e : (fun p : (∀ i,A i) × A j => Function.update p.1 j p.2) ⁻¹' (Set.pi (s : Set ℕ) t)
          = (Set.pi (s : Set ℕ) t) ×ˢ Set.univ := by
      ext p; change (∀ i∈s,Function.update p.1 j p.2 i∈t i) ↔ (∀ i∈s,p.1 i∈t i) ∧ True
      simp only [and_true]; apply forall_congr'; intro i
      apply forall_congr'; intro hi; rw [Function.update_of_ne (show i≠j from (fun h => hj (h ▸ hi)))]
    rw [e,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi μ (fun i _ => ht i)]

theorem lower_resample (μ : ∀ j, Measure (A j)) [∀ j,IsProbabilityMeasure (μ j)] (j : ℕ)
    {E : Set (∀ i,A i)} (hm : MeasurableSet E) (p : ℝ≥0∞)
    (low : ∀ x, p≤μ j {s | Function.update x j s∈E}) :
    p≤Measure.infinitePi μ E := by
  rw [←resample μ j,Measure.map_apply measurable_update' hm,Measure.prod_apply (measurable_update' hm)]
  change p≤∫⁻ x,μ j {s | Function.update x j s∈E} ∂Measure.infinitePi μ
  simpa using (lintegral_mono (μ:=Measure.infinitePi μ) (f:=fun _ => p) (fun x => low x))

def recurring {X : Type*} (E : ℕ → Set X) := {x | ∀ n,∃ j≥n,x∈E j}

theorem recurring_lower {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (E : ℕ → Set X) (h : ∀ j,MeasurableSet (E j)) (p : ℝ≥0∞)
    (low : ∀ n,∃ j≥n,p≤μ (E j)) : p≤μ (recurring E) := by
  let U := fun n => ⋃ j≥n,E j
  have eq : recurring E=⋂ n,U n := by ext x; simp [recurring,U]
  have ant : Antitone U := by
    intro n m nm x hx
    simp only [U,Set.mem_iUnion] at hx ⊢
    obtain ⟨j,hj,e⟩ := hx
    exact ⟨j,nm.trans hj,e⟩
  rw [eq,ant.measure_iInter (fun n => (MeasurableSet.iUnion (fun j =>
    MeasurableSet.iUnion (fun _ => h j))).nullMeasurableSet) ⟨0,measure_ne_top _ _⟩]
  apply le_iInf; intro n
  obtain ⟨j,hj,b⟩ := low n
  exact b.trans (measure_mono (fun x hx => Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,hx⟩⟩))

/-- The same fixed parameter has large marginal probabilities at arbitrarily late indices
and positive probability of failure at infinitely many indices on a single seed. -/
theorem fixed_parameter {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (ν : Measure X) (μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (E : ℕ → Set (X × Ω)) (h : ∀ j,MeasurableSet (E j))
    (low : ∀ j, (6/25:ℝ≥0∞)≤(ν.prod μ) (E j)) :
    ∃ x, (∀ n,∃ j≥n, (1/5:ℝ≥0∞)≤μ ((Prod.mk x) ⁻¹' E j)) ∧
      (1/5:ℝ≥0∞)≤μ (recurring (fun j => (Prod.mk x) ⁻¹' E j)) := by
  classical
  let v := fun j x => μ ((Prod.mk x) ⁻¹' E j)
  let F := fun j => {x | (1/5:ℝ≥0∞)≤v j x}
  have mv j : Measurable (v j) := measurable_measure_prodMk_left (h j)
  have mf j : MeasurableSet (F j) := measurableSet_le measurable_const (mv j)
  have many j : (1/25:ℝ≥0∞)≤ν (F j) := by
    have bound (x) : v j x≤1/5+(F j).indicator (fun _ => (1:ℝ≥0∞)) x := by
      by_cases ins : x∈F j
      · rw [Set.indicator_of_mem ins]; exact (prob_le_one).trans (le_add_self)
      · rw [Set.indicator_of_notMem ins,add_zero]; exact le_of_not_ge ins
    have int := lintegral_mono (μ:=ν) bound
    rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one] at int
    change _≤1/5+∫⁻ x,(F j).indicator 1 x ∂ν at int
    rw [lintegral_indicator_one (mf j)] at int
    have b := low j
    rw [Measure.prod_apply (h j)] at b
    change _≤∫⁻ x,v j x ∂ν at b
    have c := b.trans int
    apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _)).mp
    have cr := ENNReal.toReal_mono (by finiteness : (1/5:ℝ≥0∞)+ν (F j)≠⊤) c
    rw [ENNReal.toReal_add (by finiteness) (measure_ne_top _ _)] at cr
    norm_num [ENNReal.toReal_div] at cr ⊢
    linarith
  have pos := recurring_lower ν F mf (1/25) (fun n => ⟨n,le_rfl,many n⟩)
  have nz : ν (recurring F) ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1/25) pos)
  obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero nz
  exact ⟨x,hx,recurring_lower μ _ (fun j => measurable_prodMk_left (h j)) _ hx⟩
end Lemmata.FrankWolfePS.RandomHilbert
