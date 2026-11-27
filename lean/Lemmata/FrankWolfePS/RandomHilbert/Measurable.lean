module
public import Lemmata.FrankWolfePS.RandomHilbert.Oracle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
/-! Joint measurability in the sampled body, the seed and the whole finite history. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Filter Finset MeasureTheory TopologicalSpace
open scoped Topology BigOperators RealInnerProductSpace
noncomputable instance horizSep : SeparableSpace Horiz := by
  let U := ⋃ j,Set.range (lp.single (E:=Block) 2 j)
  let S := Submodule.span ℝ U
  have se : IsSeparable U := isSeparable_iUnion.mpr (fun j => isSeparable_range
    ((lp.singleContinuousLinearMap ℝ Block 2 j).continuous))
  have dense : S.topologicalClosure=⊤ := by
    apply top_unique; intro x _
    apply S.isClosed_topologicalClosure.mem_of_tendsto (lp.hasSum_single (p:=2) (by norm_num) x)
    apply Eventually.of_forall; intro t
    apply S.le_topologicalClosure
    exact S.sum_mem fun j _ => Submodule.subset_span (Set.mem_iUnion.mpr ⟨j,x j,rfl⟩)
  have h := (se.span (R:=ℝ)).closure
  change IsSeparable (closure (S : Set Horiz)) at h
  rw [←S.topologicalClosure_coe,dense] at h
  exact isSeparable_univ_iff.mp h
noncomputable instance horizMS : MeasurableSpace Horiz := borel _
instance horizBorel : BorelSpace Horiz := ⟨rfl⟩
noncomputable instance worldMS : MeasurableSpace World := borel _
instance worldBorel : BorelSpace World := ⟨rfl⟩

private theorem finite_evaluate {A Z V : Type*} [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace Z] [MeasurableSpace V] {g : Z → A} (hg : Measurable g)
    (F : A → Z → V) (hF : ∀ a,Measurable (F a)) : Measurable (fun x => F (g x) x) := by
  intro t ht
  have e : (fun x => F (g x) x) ⁻¹' t = ⋃ a,(g ⁻¹' {a}) ∩ ((F a) ⁻¹' t) := by
    ext x; simp
  rw [e]; exact MeasurableSet.iUnion (fun a => (hg (measurableSet_singleton a)).inter (hF a ht))

private theorem unit_meas : Measurable (unit : World → World) := by
  unfold unit; fun_prop
private theorem raw_meas (j) (i : Label j) : Measurable (fun q : World => raw q j i) := by
  have ev : Continuous (fun x : Horiz => x j) := (lp.evalCLM ℝ Block 2 j).continuous
  have ev2 := PiLp.continuous_apply 2 (fun _ : Label j => ℝ) i
  exact measurable_const.mul (ev2.measurable.comp (ev.measurable.comp ((WithLp.continuous_snd 2 ℝ Horiz).measurable.comp unit_meas)))

private theorem selectedM (j) :
    Measurable (fun x : Data × World => (choice x.1 x.2 j).val) := by
  let g := fun x : Data × World => x.1 j
  let F := fun (c : Datum j) (x : Data × World) =>
    arg (allowed c) (fun i => raw x.2 j i-noise 0 (spacing j) c.1 i) (kappa j)
  apply finite_evaluate (g:=g) ((measurable_pi_apply j).comp measurable_fst) F
  intro c
  apply (arg_cont (allowed c) (insert_nonempty _ _) (small j).1).measurable.comp
  apply Measurable.of_eval; intro i
  exact ((raw_meas j i).comp measurable_snd).sub measurable_const

theorem horizontal_measurable {X : Type*} [MeasurableSpace X] {F : X → Horiz}
    (m : ∀ j,Measurable (fun x => F x j)) : Measurable F := by
  apply measurable_of_tendsto_metrizable (f:=fun n x => ∑ j∈range n,lp.single 2 j (F x j))
  · intro n; apply Finset.measurable_sum; intro i _
    exact (lp.singleContinuousLinearMap ℝ Block 2 i).continuous.measurable.comp (m i)
  · apply tendsto_pi_nhds.mpr; intro x; exact (lp.hasSum_single (p:=2) (by norm_num) (F x)).tendsto_sum_nat
private theorem chosenCtr : Measurable (fun x : Data × World => ctr (choice x.1 x.2)) := by
  have hor : Measurable (fun x : Data × World => horizontal (choice x.1 x.2)) := by
    apply horizontal_measurable; intro i
    exact (measurable_const (a:=amp i)).smul
      ((PiLp.continuous_toLp 2 (fun _ : Label i => ℝ)).measurable.comp (selectedM i))
  exact (WithLp.prod_continuous_toLp 2 ℝ Horiz).measurable.comp (measurable_const.prodMk hor)
private theorem chosenRad : Measurable (fun x : Data × World => rad (choice x.1 x.2)) := by
  apply measurable_const.add; apply Measurable.tsum; intro j
  let g := fun x : Data × World => x.1 j
  apply finite_evaluate (g:=g) ((measurable_pi_apply j).comp measurable_fst)
    (fun c x => bonus c.1 (choice x.1 x.2 j).val)
  intro c; have co : Continuous (bonus c.1) := by unfold bonus linear sq; fun_prop
  exact co.measurable.comp (selectedM j)
theorem oracle_measurable : Measurable (fun x : Data × World => oracle x.1 x.2) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
    (chosenCtr.sub (chosenRad.smul (unit_meas.comp measurable_snd)))

/-- Jointly measurable rules for every finite history. Both the linear directions and
the final estimate may be arbitrary vectors in the Hilbert space. -/
structure Rules (Ω : Type*) [MeasurableSpace Ω] where
  ask : Ω → List World → World
  out : Ω → List World → World
  askM : Unique.BorelRule ask
  outM : Unique.BorelRule out
noncomputable def output {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (T : ℕ) (d : Data) (ω : Ω) :=
  M.out ω (Unique.play (oracle d) (M.ask ω) T [])

theorem output_measurable {Ω : Type*} [MeasurableSpace Ω] (M : Rules Ω) (T : ℕ) :
    Measurable (fun p : Data × Ω => output M T p.1 p.2) := by
  have aux (n : ℕ) {m : ℕ} (h : Data × Ω → Fin m → World) (hh : Measurable h) :
      Measurable (fun p : Data × Ω => M.out p.2 (Unique.play (oracle p.1) (M.ask p.2) n (List.ofFn (h p)))) := by
    induction n generalizing m with
    | zero => exact (M.outM m).comp (measurable_snd.prodMk hh)
    | succ t ih =>
      let y := fun p : Data × Ω => oracle p.1 (M.ask p.2 (List.ofFn (h p)))
      have yy : Measurable y := oracle_measurable.comp (measurable_fst.prodMk ((M.askM m).comp (measurable_snd.prodMk hh)))
      let k : Data × Ω → Fin (m+1) → World := fun p => Fin.cons (y p) (h p)
      have mk : Measurable k := by
        apply Measurable.of_eval; intro i; refine Fin.cases ?_ (fun j => ?_) i
        · simpa [k] using yy
        · simpa [k,Function.comp_def] using (measurable_pi_apply j).comp hh
      simpa [Unique.play,k,List.ofFn_succ,y] using ih k mk
  simpa [output] using aux T (m:=0) (fun _ => fun i => Fin.elim0 i) measurable_const
end Lemmata.FrankWolfePS.RandomHilbert
