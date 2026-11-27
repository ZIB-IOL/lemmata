module
public import Lemmata.FrankWolfePS.RandomHilbert.Projection
public import Lemmata.FrankWolfePS.RandomHilbert.Measurable
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform
/-! One independent block prior, fixed for all methods and all budgets. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open MeasureTheory Finset
open scoped ENNReal BigOperators
def shell (j : ℕ) := instanceSets (budget j) (0:Label j)
abbrev Sample (j : ℕ) := Table j × ↥(shell j)
abbrev Tape := ∀ j, Sample j
theorem label_card (j : ℕ) : Fintype.card (Label j)=256*(budget j+1) := by simp [Label]
instance (j : ℕ) : Nonempty (Sample j) := by
  have sh : (shell j).Nonempty := by
    apply powersetCard_nonempty.mpr; simp; omega
  exact ⟨(0, ⟨sh.choose,sh.choose_spec⟩)⟩
noncomputable def marginal (j : ℕ) : Measure (Sample j) := Measure.uniformOfFinset univ
private theorem uniform_probability (X : Type*) [Fintype X] [Nonempty X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : IsProbabilityMeasure (Measure.uniformOfFinset (univ : Finset X)) := by
  classical
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ,Finset.filter_true,card_univ]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
instance (j : ℕ) : IsProbabilityMeasure (marginal j) := uniform_probability (Sample j)
noncomputable def prior : Measure Tape := Measure.infinitePi marginal
instance : IsProbabilityMeasure prior := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi marginal))
def data (x : Tape) : Data := fun j => ((x j).1, insert 0 (x j).2.val)
theorem data_meas : Measurable data := by
  apply Measurable.of_eval; intro i
  exact (measurable_of_countable (f:=fun s : Sample i => (s.1,insert (0:Label i) s.2.val))).comp (measurable_pi_apply i)
theorem data_card (x : Tape) (j : ℕ) : (allowed (data x j)).card=8*K j := by
  simpa [data,allowed] using (Unique.shell_info (x j).2.property).2
theorem data_update (x : Tape) (j : ℕ) (s : Sample j) :
    data (Function.update x j s)=withBlock (data x) j (insert 0 s.2.val) s.1 := by
  funext i; by_cases h : i=j
  · subst i; simp [data,withBlock]
  · simp [data,withBlock,Function.update_of_ne h]

private theorem play_drop {E : Type*} (o : E → E) (a : List E → E) (n : ℕ) (h : List E) :
    (Unique.play o a n h).drop n=h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => rw [Unique.play,←List.drop_drop (i:=1) (j:=n),ih]; rfl
private theorem play_more {E : Type*} (o : E → E) (a : List E → E) (n m : ℕ) (h : List E) :
    Unique.play o a (n+m) h = Unique.play o a m (Unique.play o a n h) := by
  induction n generalizing h with
  | zero => simp [Unique.play]
  | succ n ih => rw [Nat.succ_add,Unique.play,Unique.play,ih]

def evidence {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (j T : ℕ) : Set (Tape × Ω) :=
  {p | distant j (data p.1 j).2 (output M T (data p.1) p.2)}
theorem evidence_meas {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (j T : ℕ) :
    MeasurableSet (evidence M j T) := by
  let f := fun p : Tape × Ω => output M T (data p.1) p.2
  have mf : Measurable f := (output_measurable M T).comp ((data_meas.comp measurable_fst).prodMk measurable_snd)
  have ex : Continuous (extract j) := (continuous_const (y:=(amp j)⁻¹)).smul
    ((lp.evalCLM ℝ Block 2 j).continuous.comp (WithLp.continuous_snd 2 ℝ Horiz))
  have b : Measurable (fun p : Tape × Ω => liftVec (simplexBarycenter (insert (0:Label j) (data p.1 j).2))) :=
    (measurable_of_countable (f:=fun s : Sample j => liftVec (simplexBarycenter (insert (0:Label j) (insert 0 s.2.val))))).comp
      ((measurable_pi_apply j).comp measurable_fst)
  exact measurableSet_le measurable_const (((ex.measurable.comp mf).sub b).norm.pow_const 2)

theorem count_coordinate {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (ω : Ω) (x : Tape)
    (j T : ℕ) (le : T≤budget j) :
    (Fintype.card (Sample j):ℝ)*6/25 ≤ ∑ s : Sample j, flag ((Function.update x j s,ω)∈evidence M j T) := by
  classical
  let n := budget j-T
  let ask := M.ask ω
  let get := fun h : List World => extract j (M.out ω (h.drop n))
  let est : List World → Pt (Label j) := fun h => ((get h).ofLp,0)
  have count := (block_scanner (data x) j).estimation ask est (spacing_pos j).le (small j).2.1 (label_card j)
  have pad (o : World → World) : (Unique.play o ask (budget j) []).drop n=Unique.play o ask T [] := by
    have eq : budget j=T+n := by dsimp [n]; omega
    rw [show Unique.play o ask (budget j) []=Unique.play o ask n (Unique.play o ask T []) by rw [eq,play_more]]
    exact play_drop o ask n _
  rw [Fintype.sum_prod_type]; simp only [Fintype.card_prod,Nat.cast_mul,Fintype.card_coe]
  apply count.trans
  apply sum_le_sum; intro D _
  rw [←Finset.sum_coe_sort]
  apply sum_le_sum; intro J _
  apply le_of_eq; apply congrArg flag; apply propext
  change (1/(128*((budget j+1:ℕ):ℝ))≤sq (fun i =>
    (get (Unique.play (oracle (withBlock (data x) j (insert 0 J.val) D)) ask (budget j) [])) i-
      simplexBarycenter (insert 0 J.val) i)) ↔ _
  simp only [evidence,Set.mem_ofPred_eq,distant,data_update,withBlock,Function.update_self,insert_idem,budget_succ]
  change (1/(128*(K j:ℝ))≤sq _) ↔ (1/(128*(K j:ℝ))≤‖_ - _‖^2)
  unfold get
  rw [pad,EuclideanSpace.real_norm_sq_eq]
  rfl

theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (ω : Ω) (x : Tape)
    (j T : ℕ) (le : T≤budget j) :
    (6/25:ℝ≥0∞)≤marginal j {s | (Function.update x j s,ω)∈evidence M j T} := by
  classical
  let ev := fun s : Sample j => (Function.update x j s,ω)∈evidence M j T
  have b := count_coordinate M ω x j T le
  change _≤∑ s : Sample j,flag (ev s) at b
  simp only [flag,Finset.sum_boole] at b
  change (6/25:ℝ≥0∞)≤Measure.uniformOfFinset (univ:Finset (Sample j)) {s | ev s}
  rw [Measure.uniformOfFinset_apply]
  simp only [Finset.card_univ,Set.mem_ofPred_eq]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast]
  norm_num only [ENNReal.toReal_ofNat]
  apply (le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  linarith only [b]
end Lemmata.FrankWolfePS.RandomHilbert
