module

public import Lemmata.FrankWolfePS.Lower.Body
@[expose] public section

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
open scoped BigOperators Pointwise RealInnerProductSpace
variable {ι : Type*} [Fintype ι]
section Coordinates
variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem feasible_compact (I : Finset ι) {R : ℝ} (hR : 0 < R) :
    IsCompact {z | Feasible R I z} := by
  have hc : Continuous (coords (ι := ι)) := by
    exact (continuous_pi fun i => PiLp.continuous_apply 2 _ (some i)).prodMk
      (PiLp.continuous_apply 2 _ none)
  have eq : {z | Feasible R I z} = coords '' Rounded (core R I) R := by
    ext z
    constructor
    · intro hz; exact ⟨embed z, (feasible_iff_rounded hR I z).mp hz, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact (feasible_iff_rounded hR I _).mpr (by simpa using hw)
  rw [eq]; exact (body_compact_convex I R).1.image hc

omit [DecidableEq ι] in
theorem obj_continuous (R : ℝ) : Continuous (obj (ι := ι) R) := by
  unfold obj sq
  fun_prop

theorem min_attained {R : ℝ} (hR : 0 < R) {I : Finset ι} (ne : I.Nonempty) :
    ∃ z, Feasible R I z ∧ obj R z = optimum R I := by
  obtain ⟨i, hi⟩ := ne
  obtain ⟨z, hz, hm⟩ := (feasible_compact I hR).exists_isMinOn
    ⟨_, anchor_feasible R hi⟩ (obj_continuous R).continuousOn
  refine ⟨z, hz, Eq.symm (IsLeast.csInf_eq ?_)⟩
  refine ⟨⟨z, hz, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hm hw

def scalePt (a : ℝ) (z : Pt ι) : Pt ι := (fun i => a * z.1 i, a * z.2)
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem scale_scale (b a : ℝ) (z : Pt ι) : scalePt b (scalePt a z) = scalePt (b * a) z := by
  ext i <;> simp [scalePt, mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem scale_one (z : Pt ι) : scalePt 1 z = z := by ext i <;> simp [scalePt]

omit [Fintype ι] [DecidableEq ι] in
theorem scale_embed (a : ℝ) (z : Pt ι) : embed (scalePt a z) = a • embed z := by
  ext i
  cases i <;> rfl

omit [DecidableEq ι] in
theorem obj_scale (a r : ℝ) (ha : 0 < a) (z : Pt ι) :
    obj r (scalePt a z) = a ^ 2 * obj (r / a) z := by
  simp only [obj, scalePt, sq, mul_pow, ← mul_sum]
  field_simp

def physicalBody (a r : ℝ) (I : Finset ι) : Set (Ambient ι) :=
  a • Rounded (core (r / a) I) (r / a)

omit [DecidableEq ι] in
theorem physical_feasible_iff {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (I : Finset ι) (z : Pt ι) :
    embed z ∈ physicalBody a r I ↔ Feasible (r / a) I (scalePt a⁻¹ z) := by
  rw [feasible_iff_rounded (div_pos hr ha), scale_embed]
  constructor
  · rintro ⟨w, hw, he⟩
    rw [← he, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]; exact hw
  · intro h
    exact ⟨a⁻¹ • embed z, h, by simp [smul_smul, ha.ne']⟩

omit [DecidableEq ι] in
theorem physical_parallel {a r : ℝ} (ha : 0 < a) (I : Finset ι) :
    physicalBody a r I = Rounded (a • core (r / a) I) r := by
  have h (w v : Ambient ι) : ‖a • w - a • v‖ = a * ‖w - v‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, hb⟩, rfl⟩
    refine ⟨a • v, ⟨v, hv, rfl⟩, ?_⟩
    rw [h, mul_comm]
    exact (le_div_iff₀ ha).mp hb
  · rintro ⟨_, ⟨v, hv, rfl⟩, hz⟩
    refine ⟨a⁻¹ • z, ⟨v, hv, ?_⟩, by simp [smul_smul, ha.ne']⟩
    apply (le_div_iff₀ ha).mpr
    rw [mul_comm, ← h]
    simpa [smul_smul, ha.ne'] using hz

theorem physical_parameters {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (I : Finset ι) (hI : 1 < I.card) :
    Metric.diam (physicalBody a r I) = 2 * r + Real.sqrt 2 * a ∧
    ∀ z ∈ physicalBody a r I, ∀ w ∈ physicalBody a r I, ∀ n m : Ambient ι, ‖n‖ = 1 → ‖m‖ = 1 →
    Supports (physicalBody a r I) z n → Supports (physicalBody a r I) w m →
    ‖n - m‖ ≤ (1 / r) * ‖z - w‖ := by
  constructor
  · rw [physicalBody, diam_smul₀, body_diameter I hI _ (div_pos hr ha), Real.norm_eq_abs,
      abs_of_pos ha]
    field_simp
  · rw [physical_parallel ha]; exact fun _ hz _ hw _ _ hn hm hs ht =>
      rounded_lipschitz_normals hr hz hw hn hm hs ht

noncomputable def physicalOpt (L a r : ℝ) (I : Finset ι) :=
  sInf ((fun z : Pt ι => L * obj r z) '' {z | embed z ∈ physicalBody a r I})

theorem physicalOpt_eq {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) {I : Finset ι}
    (hne : I.Nonempty) :
    physicalOpt L a r I = L * a ^ 2 * optimum (r / a) I := by
  obtain ⟨v, hv, hm⟩ := min_attained (div_pos hr ha) hne
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨scalePt a v, (physical_feasible_iff ha hr I _).mpr (by simpa [ha.ne'] using hv), ?_⟩
    change L * obj r (scalePt a v) = _
    rw [obj_scale _ _ ha, hm]; ring
  · rintro _ ⟨z, hz, rfl⟩
    have hf := (physical_feasible_iff ha hr I z).mp hz
    have lb := csInf_le (objective_bddBelow (div_pos hr ha) I) ⟨_, hf, rfl⟩
    change optimum (r / a) I ≤ obj (r / a) (scalePt a⁻¹ z) at lb
    have he := obj_scale a r ha (scalePt a⁻¹ z)
    simp [ha.ne'] at he
    change _ ≤ L * obj r z
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left lb (by positivity)

def physicalFailure (L a r : ℝ) (k : ℕ) (I : Finset ι) (z : Pt ι) : Prop :=
  embed z ∉ physicalBody a r I ∨ L * a ^ 2 / (16 * (k : ℝ)) ≤ L * obj r z - physicalOpt L a r I

theorem failure_scale {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r)
    (k : ℕ) {I : Finset ι} (hne : I.Nonempty) (z : Pt ι) :
    physicalFailure L a r k I z ↔ failure (r / a) k I (scalePt a⁻¹ z) := by
  rw [physicalFailure, failure, physical_feasible_iff ha hr, physicalOpt_eq hL ha hr hne]
  apply or_congr_right
  have he := obj_scale a r ha (scalePt a⁻¹ z)
  simp [ha.ne'] at he
  rw [he, ← mul_assoc, ← mul_sub, show L * a ^ 2 / (16 * (k : ℝ)) =
      L * a ^ 2 * (1 / (16 * (k : ℝ))) by ring]
  exact mul_le_mul_iff_right₀ (by positivity)

end Coordinates
section
variable [LinearOrder ι]

/-- The vertex oracle of the physical body: the scaled normalized replies. -/
noncomputable def physOracle (a r : ℝ) (anchor : ι) (I : Finset ι) (q : Ambient ι) : Ambient ι :=
  a • oracle (r / a) anchor I q

/-- The coordinates of the point a method returns against the physical vertex oracle. -/
noncomputable abbrev Method.physicalRun {t} (s : Method (Ambient ι) t) (a r : ℝ) (anchor : ι)
    (I : Finset ι) : Pt ι :=
  coords (s.run (physOracle a r anchor I))

/-- Rescaling a method: replies are multiplied by `a`, the output divided by `a`. -/
noncomputable def Method.simulate {t} (s : Method (Ambient ι) t) (a : ℝ) : Method (Ambient ι) t :=
  match s with
  | .ret z => .ret (a⁻¹ • z)
  | .ask q next => .ask q fun w => (next (a • w)).simulate a

omit [Fintype ι] [LinearOrder ι] in
/-- Running a rescaled method: the replies are rescaled, the output scaled back. -/
theorem Method.simulate_run_eq {t} (s : Method (Ambient ι) t) (a : ℝ) (O : Ambient ι → Ambient ι) :
    (s.simulate a).run O = a⁻¹ • s.run (fun q => a • O q) := by
  induction s with
  | ret z => rfl
  | ask q next ih => simp [simulate, Method.run, ih]

theorem Method.simulate_run {t} (s : Method (Ambient ι) t) (a r : ℝ) (anchor : ι) (I : Finset ι) :
    coords ((s.simulate a).run (oracle (r / a) anchor I)) =
      scalePt a⁻¹ (s.physicalRun a r anchor I) := by
  induction s with
  | ret z =>
    simp only [simulate, Method.run, Method.physicalRun]
    rw [show a⁻¹ • z = embed (scalePt a⁻¹ (coords z)) by rw [scale_embed, embed_coords],
      coords_embed]
  | ask q next ih =>
    simpa [simulate, Method.run, Method.physicalRun, physOracle] using ih _

theorem physical_oracle_correct {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (anchor : ι) {I : Finset ι}
    (hI : anchor ∈ I) (q : Ambient ι) :
    a • oracle (r / a) anchor I q ∈ physicalBody a r I ∧ ∀ v ∈ physicalBody a r I,
    ⟪q, a • oracle (r / a) anchor I q⟫ ≤ ⟪q, v⟫ := by
  have ⟨hf, hm⟩ := oracle_correct (r / a) (div_pos hr ha) anchor I hI q
  refine ⟨⟨_, hf, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  simpa [real_inner_smul_right] using mul_le_mul_of_nonneg_left (hm v hv) ha.le

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The scaled minimax theorem, for numerical adaptive queries and any tape law.
The seed measurability hypothesis is exactly the finite set of failure events. -/
theorem scaled_randomized_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L a r : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Method (Ambient ι) T)
    (meas : ∀ S ∈ shells T anchor, MeasurableSet {ω | physicalFailure L a r (T + 1)
      (insert anchor S) ((s ω).physicalRun a r anchor (insert anchor S))}) :
    (↑(shells T anchor).card : ℝ) / 4 ≤ ∑ S ∈ shells T anchor,
      μ.real {ω | physicalFailure L a r (T + 1) (insert anchor S)
        ((s ω).physicalRun a r anchor (insert anchor S))} ∧
      ∃ S ∈ shells T anchor, 1 / 4 ≤ μ.real {ω | physicalFailure L a r (T + 1) (insert anchor S)
        ((s ω).physicalRun a r anchor (insert anchor S))} := by
  have ex (S : Finset ι) : {ω | physicalFailure L a r (T + 1) (insert anchor S)
      ((s ω).physicalRun a r anchor (insert anchor S))} =
      {ω | failure (r / a) (T + 1) (insert anchor S)
        (coords (((s ω).simulate a).run (oracle (r / a) anchor (insert anchor S))))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Method.simulate_run]
    exact failure_scale hL ha hr _ (insert_nonempty _ _) _
  simpa only [ex] using numerical_randomized_lower_bound T anchor hN (r / a) (div_pos hr ha) μ
    (fun ω => (s ω).simulate a) (by simpa only [ex] using meas)
end
end Lemmata.FrankWolfePS
