module

public import Lemmata.FrankWolfePS.Unique.Prescribed
public import Lemmata.FrankWolfePS.Lower.Feasible

@[expose] public section

/-!
# Feasible methods on the family without tie-breaking

If a method returns a feasible point on every jittered body, the simulator of the base family
returns repaired points, which are feasible on every base body. The base estimate for feasible
runs (at least `97/128` of the instances fail, for each tape) transfers through the simulation:
at least `97/128 · 99/100 ≥ 3/4` of the jittered instances fail at the threshold of the main
theorem. At prescribed parameters this gives probability `3/4` instead of `1/5`, and an expected
gap of `3/4` of the threshold.
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset MeasureTheory
open scoped BigOperators Pointwise

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The repair of a point of a jittered body lies in the base body. -/
theorem repaired_feasible {A : ℝ} (hA : 0 < A) {a : ι} (T : ℕ) (D : Draw ι T) {I : Finset ι}
    (ai : a ∈ I) {x : Ambient ι} (hx : x ∈ instanceBody A a T D I) :
    Feasible (1 / A) I (scalePt A⁻¹ (coords (repaired A a (2 * jitter A T) x))) := by
  have P := settings hA ι T
  obtain ⟨z, hz, hd⟩ := near_old hA P.2.2.1.le (vtx_near hA a T D) hx
  have ball : ∀ y, ‖y - baseV A a‖ ≤ 1 → y ∈ Old A I := fun y hy =>
    (mem_old hA I y).mpr ⟨atom a, atom_base ai, by simpa [baseV] using hy⟩
  have xm : repaired A a (2 * jitter A T) x ∈ Old A I :=
    repair_mem (physical_body_compact_convex I).2 ball (mul_pos two_pos P.1) hz
      (hd.trans P.2.2.2.2.1)
  exact (physical_feasible_iff hA one_pos I _).mp (by rw [embed_coords]; exact xm)

/-- **Feasible methods on the jittered family, fixed tape.** If the rules return a feasible point
on every instance, at least `3/4` of the instances fail at threshold `θ`. -/
theorem unique_feasible_fixed_tape {A θ : ℝ} (hA : 0 < A) (a : ι) (T : ℕ)
    (hN : Fintype.card ι = 256 * (T + 1))
    (hθ : θ + (A + 35) * (2 * A + 5) * (2 * jitter A T) ≤ A ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)))
    (ask : Hist ι → Ambient ι) (out : Hist ι → Ambient ι)
    (feas : ∀ d ∈ ensemble ι a T,
      outcome A a T d.1 (insert a d.2) ask out ∈ instanceBody A a T d.1 (insert a d.2)) :
    ((ensemble ι a T).card : ℝ) * (3 / 4) ≤ ∑ d ∈ ensemble ι a T,
      flag (Bad (instanceBody A a T d.1 (insert a d.2)) θ
        (outcome A a T d.1 (insert a d.2) ask out)) := by
  classical
  let η := jitter A T
  let b := step A ι T
  let s := smooth A ι T
  let H := instanceSets T a
  let M := (Fintype.card (Draw ι T) : ℝ)
  let B := trouble (Q := alphabet ι T) A a b s (start A a) ask T {a} (fun _ => [])
  let E := fun (D : Draw ι T) (J : Finset ι) =>
    Bad (instanceBody A a T D (insert a J)) θ (outcome A a T D (insert a J) ask out)
  have P := settings hA ι T
  have each (D : Draw ι T) : (H.card : ℝ) * (97 / 128) ≤
      (∑ J ∈ H, flag (E D J)) + (H.card : ℝ) * (97 / 128) * flag (B D) := by
    by_cases trouble' : B D
    · have one : flag (B D) = 1 := by simp [flag, trouble']
      rw [one, mul_one]
      have := sum_nonneg (fun J (_ : J ∈ H) => flag_nonneg (E D J))
      linarith
    · simp only [flag, ite_eq_right trouble', mul_zero, add_zero]
      let o : Hist ι → Pt ι := fun x => scalePt A⁻¹ (coords (repaired A a (2 * η) (out x)))
      let tree := simulate A a b s (start A a) ask o D T {a} []
      have rep (J : Finset ι) (hJ : J ∈ H) : tree.run (insert a J) =
          o (play (reply (instanceBody A a T D (insert a J)) (start A a)) ask T []) :=
        replay A a P.2.2.1 (start A a) ask o (insert a J) D
          (fun R h => vtx_anchor hA a T D h) T (R := {a}) (mem_singleton_self a)
          (singleton_subset_iff.mpr (shell_info hJ).1) (h := fun _ => []) trouble'
      have tfeas : ∀ J ∈ H, Feasible (1 / A) (insert a J) (tree.run (insert a J)) := by
        intro J hJ
        rw [rep J hJ]
        exact repaired_feasible hA T D (shell_info hJ).1
          (feas (D, J) (mem_product.mpr ⟨mem_univ _, hJ⟩))
      have H1 := feasible_fixed_tape T a hN (by positivity : (0 : ℝ) < 1 / A) tree tfeas
      apply H1.trans
      apply sum_le_sum; intro J hJ
      have hi := shell_info hJ
      have impl : failure (1 / A) (T + 1) (insert a J) (tree.run (insert a J)) → E D J := by
        intro f
        rw [rep J hJ] at f
        have f' := (failure_scale one_pos hA one_pos (T + 1) (insert_nonempty a J) _).mpr f
        exact loss_transfer hA hi.1 P.2.2.1.le (mul_pos two_pos P.1) P.2.2.2.2.2.1
          P.2.2.2.2.1 hθ (vtx_near hA a T D) f'
      by_cases f : failure (1 / A) (T + 1) (insert a J) (tree.run (insert a J))
      · simp only [flag, ite_eq_left f, ite_eq_left (impl f), le_refl]
      · simp only [flag, ite_eq_right f]; split <;> norm_num
  have all := sum_le_sum (s := (univ : Finset (Draw ι T))) (fun D _ => each D)
  rw [sum_add_distrib] at all
  have e1 : ∑ _D : Draw ι T, (H.card : ℝ) * (97 / 128) = M * ((H.card : ℝ) * (97 / 128)) := by
    simp [M]
  have e2 : ∑ D : Draw ι T, (H.card : ℝ) * (97 / 128) * flag (B D) =
      (H.card : ℝ) * (97 / 128) * countP B := by
    rw [← mul_sum]; rfl
  rw [e1, e2] at all
  have bar : countP B ≤ M / 100 := bad_table_count hA a T ask
  have hbar := mul_le_mul_of_nonneg_left bar (by positivity : 0 ≤ (H.card : ℝ) * (97 / 128))
  simp only [ensemble, card_product, card_univ, Nat.cast_mul, sum_product]
  change M * (H.card : ℝ) * (3 / 4) ≤ ∑ D, ∑ J ∈ H, flag (E D J)
  nlinarith only [all, hbar, mul_nonneg (by dsimp [M]; positivity : 0 ≤ M) (Nat.cast_nonneg H.card)]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Feasible methods on the jittered family.** For a measurable randomized method requiring no
more than `T` calls that returns a feasible point on every instance, some instance, chosen before
the tape, makes the method fail at threshold `θ` with probability at least `3/4`. -/
theorem unique_feasible_lower_bound {A θ : ℝ} (hA : 0 < A) (a : ι) (T : ℕ)
    (hN : Fintype.card ι = 256 * (T + 1))
    (hθ : θ + (A + 35) * (2 * A + 5) * (2 * jitter A T) ≤ A ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T)
    (hs : Method.IsMeasurable s)
    (feas : ∀ D : Draw ι T, ∀ J ∈ instanceSets T a, ∀ ω,
      (s ω).run (reply (instanceBody A a T D (insert a J)) (start A a)) ∈
        instanceBody A a T D (insert a J)) :
    ∃ D : Draw ι T, ∃ J ∈ instanceSets T a, 3 / 4 ≤ μ.real {ω |
      Bad (instanceBody A a T D (insert a J)) θ
        ((s ω).run (reply (instanceBody A a T D (insert a J)) (start A a)))} := by
  classical
  let H := ensemble ι a T
  let C := fun d : Draw ι T × Finset ι => instanceBody A a T d.1 (insert a d.2)
  let e := fun d : Draw ι T × Finset ι => {ω | Bad (C d) θ ((s ω).run (reply (C d) (start A a)))}
  have sh : (instanceSets T a).Nonempty := by
    apply powersetCard_nonempty.mpr; simp [hN]; omega
  let : NeZero (alphabet ι T) := ⟨by unfold alphabet; omega⟩
  have ne : H.Nonempty := Finset.univ_nonempty.product sh
  have m (d) (hd : d ∈ H) : MeasurableSet (e d) := by
    have si := shell_info (mem_product.mp hd).2
    have size : 1 < (insert a d.2).card := by rw [si.2]; omega
    have spec := fixed_instance_spec hA a T d.1 si.1 size
    have outM := hs _ spec.2.2.2.2.2.2.2.2.1
    have cont : Continuous (cost (ι := ι)) := by unfold cost quadratic; fun_prop
    exact ((spec.1.isClosed.measurableSet.preimage outM).compl).union (measurableSet_le
      measurable_const ((cont.measurable.comp outM).sub measurable_const))
  have fixed (ω : Ω) : (H.card : ℝ) * (3 / 4) ≤ ∑ d ∈ H, flag (ω ∈ e d) := by
    have h := unique_feasible_fixed_tape hA a T hN hθ (fun h => (s ω).queryAfter h.reverse)
      (fun h => (s ω).outAfter h.reverse) (fun d hd => by
        simp only [outcome, Method.outAfter_play _ _ (le_refl T)]
        exact feas d.1 d.2 (mem_product.mp hd).2 ω)
    simp only [outcome, Method.outAfter_play _ _ (le_refl T)] at h
    simpa [e, C] using h
  obtain ⟨⟨D, J⟩, hj, hp⟩ := select_tape H ne μ (3 / 4) e m fixed
  exact ⟨D, J, (mem_product.mp hj).2, hp⟩

/-- **Feasible methods without tie-breaking, at prescribed parameters.** If the method returns a
feasible point on every rescaled jittered body, one of them, chosen before the tape, gives gap at
least `L (D - 2/β)² / (64 (T + 1))` with probability at least `3/4`, and expected gap at least
`3/4` of that threshold. -/
theorem prescribed_unique_feasible (T : ℕ) (a : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L β D : ℝ} (hL : 0 < L) (hβ : 0 < β) (hD : 2 < β * D) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T) (hs : Method.IsMeasurable s)
    (feas : ∀ Dt : Draw ι T, ∀ J ∈ instanceSets T a, ∀ ω,
      (s ω).run (reply ((1 / β) • instanceBody (unitScale β D) a T Dt (insert a J))
        (hardStart β D a)) ∈ (1 / β) • instanceBody (unitScale β D) a T Dt (insert a J)) :
    ∃ Dt : Draw ι T, ∃ J ∈ instanceSets T a,
      let C := (1 / β) • instanceBody (unitScale β D) a T Dt (insert a J)
      3 / 4 ≤ μ.real {ω | L * (D - 2 / β) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)) ≤
          hardObjective L (1 / β) ((s ω).run (reply C (hardStart β D a))) -
            sInf (hardObjective L (1 / β) '' C)} ∧
      3 / 4 * (L * (D - 2 / β) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ))) ≤
        ∫ ω, hardObjective L (1 / β) ((s ω).run (reply C (hardStart β D a))) -
            sInf (hardObjective L (1 / β) '' C) ∂μ := by
  have hc : 0 < 1 / β := by positivity
  have hA : 0 < unitScale β D := unitScale_pos hD
  let s' : Ω → Method (Ambient ι) T := fun ω => (s ω).simulate (1 / β)
  have hs' : Method.IsMeasurable s' := by
    intro O hO
    have h1 := (hs (fun q => (1 / β) • O q) (hO.const_smul (1 / β))).const_smul (1 / β)⁻¹
    convert h1 using 1
    funext ω
    exact Method.simulate_run_eq (s ω) (1 / β) O
  have run (Dt : Draw ι T) (J : Finset ι) (hJ : J ∈ instanceSets T a) (ω : Ω) :
      (s' ω).run (reply (instanceBody (unitScale β D) a T Dt (insert a J))
          (start (unitScale β D) a)) =
        (1 / β)⁻¹ • (s ω).run (reply ((1 / β) • instanceBody (unitScale β D) a T Dt (insert a J))
          (hardStart β D a)) := by
    simp only [s', Method.simulate_run_eq, (scaled_instance hβ hD T a Dt hJ).2.2.2.2.2.2.2.1]
  have feas' : ∀ Dt : Draw ι T, ∀ J ∈ instanceSets T a, ∀ ω,
      (s' ω).run (reply (instanceBody (unitScale β D) a T Dt (insert a J))
        (start (unitScale β D) a)) ∈ instanceBody (unitScale β D) a T Dt (insert a J) := by
    intro Dt J hJ ω
    rw [run Dt J hJ ω, ← Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    exact feas Dt J hJ ω
  obtain ⟨Dt, J, hJ, prob⟩ :=
    unique_feasible_lower_bound hA a T hN (unit_threshold hD T) μ s' hs' feas'
  obtain ⟨hcC, -, -, -, -, -, -, -, hmeas⟩ := scaled_instance hβ hD T a Dt hJ
  have runJ := run Dt J hJ
  have feasJ := feas Dt J hJ
  set C := instanceBody (unitScale β D) a T Dt (insert a J)
  have event : {ω | Bad C ((β * D - 2) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)))
      ((s' ω).run (reply C (start (unitScale β D) a)))} =
      {ω | L * (D - 2 / β) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)) ≤
        hardObjective L (1 / β) ((s ω).run (reply ((1 / β) • C) (hardStart β D a))) -
          sInf (hardObjective L (1 / β) '' ((1 / β) • C))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, runJ ω, prescribed_threshold hβ]
    rw [bad_smul hL hc C]
    exact or_iff_right (not_not.mpr (feasJ ω))
  rw [event] at prob
  refine ⟨Dt, J, hJ, prob, ?_⟩
  have zm : Measurable fun ω => (s ω).run (reply ((1 / β) • C) (hardStart β D a)) := hs _ hmeas
  have hcont : Continuous (hardObjective (ι := ι) L (1 / β)) := hardObjective_continuous L _
  have g0 : ∀ ω, 0 ≤ hardObjective L (1 / β) ((s ω).run (reply ((1 / β) • C) (hardStart β D a))) -
      sInf (hardObjective L (1 / β) '' ((1 / β) • C)) := fun ω =>
    sub_nonneg.mpr (csInf_le (hcC.image hcont).bddBelow ⟨_, feasJ ω, rfl⟩)
  have gi := (integrable_comp_of_mem_compact μ hcC hcont zm feasJ).sub
    (integrable_const (sInf (hardObjective L (1 / β) '' ((1 / β) • C))))
  have gm : MeasurableSet {ω | L * (D - 2 / β) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)) ≤
      hardObjective L (1 / β) ((s ω).run (reply ((1 / β) • C) (hardStart β D a))) -
        sInf (hardObjective L (1 / β) '' ((1 / β) • C))} :=
    measurableSet_le measurable_const ((hcont.measurable.comp zm).sub measurable_const)
  exact fraction_mul_le_integral μ gi g0 (by positivity) gm prob

end Lemmata.FrankWolfePS.Unique
