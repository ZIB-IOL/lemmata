module

public import Lemmata.FrankWolfePS.Unique.Lower

@[expose] public section

/-!
# The lower bound with unique linear minimizers, at prescribed smoothness and diameter

Rescaling the jittered family of simplex scale `A = 0.99 (βD - 2)/√2` by `1/β` gives, for every
`L, β > 0` with `βD > 2`, bodies with `β`-Lipschitz unit normals, diameter at most `D` and a
unique minimizing point in every nonzero direction. Every measurable randomized method requiring
no more than `T` calls fails on one of them, chosen before the tape, with probability at least
`1/5` at the threshold `L (D - 2/β)² / (64 (T + 1))`.
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise

section Scaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem minAt_smul {C : Set E} {c : ℝ} (hc : 0 < c) {q x : E} :
    MinAt (c • C) q (c • x) ↔ MinAt C q x := by
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨(Set.smul_mem_smul_set_iff₀ hc.ne' C x).mp hx, fun y hy => ?_⟩
    have := hm (c • y) (Set.smul_mem_smul_set hy)
    rw [real_inner_smul_right, real_inner_smul_right] at this
    exact le_of_mul_le_mul_left this hc
  · rintro ⟨hx, hm⟩
    refine ⟨Set.smul_mem_smul_set hx, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [real_inner_smul_right, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hm y hy) hc.le

theorem minAt_smul_iff {C : Set E} {c : ℝ} (hc : 0 < c) {q x : E} :
    MinAt (c • C) q x ↔ MinAt C q (c⁻¹ • x) := by
  have := minAt_smul (C := C) (q := q) (x := c⁻¹ • x) hc
  rwa [smul_inv_smul₀ hc.ne'] at this

theorem unique_smul {C : Set E} {c : ℝ} (hc : 0 < c) {q : E} (h : ∃! x, MinAt C q x) :
    ∃! x, MinAt (c • C) q x := by
  obtain ⟨x, hx, hu⟩ := h
  refine ⟨c • x, (minAt_smul hc).mpr hx, fun y hy => ?_⟩
  rw [← hu _ ((minAt_smul_iff hc).mp hy), smul_inv_smul₀ hc.ne']

theorem reply_smul {C : Set E} (hC : IsCompact C) {x₀ : E} (h0 : x₀ ∈ C) {c : ℝ} (hc : 0 < c)
    (uniq : ∀ q, q ≠ 0 → ∃! x, MinAt C q x) (q : E) :
    reply (c • C) (c • x₀) q = c • reply C x₀ q := by
  by_cases hq : q = 0
  · simp [reply, hq]
  · exact (unique_smul hc (uniq q hq)).unique (reply_min (hC.smul c) (Set.smul_mem_smul_set h0) q)
      ((minAt_smul hc).mpr (reply_min hC h0 q))

theorem supports_smul {C : Set E} {c : ℝ} (hc : 0 < c) {z n : E} :
    Supports (c • C) (c • z) n ↔ Supports C z n := by
  constructor
  · intro h w hw
    have := h (c • w) (Set.smul_mem_smul_set hw)
    rw [real_inner_smul_right, real_inner_smul_right] at this
    exact le_of_mul_le_mul_left this hc
  · rintro h _ ⟨w, hw, rfl⟩
    rw [real_inner_smul_right, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (h w hw) hc.le

theorem lipschitzNormals_smul {C : Set E} {c β : ℝ} (hc : 0 < c)
    (h : Upper.LipschitzNormals C β) : Upper.LipschitzNormals (c • C) (β / c) := by
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ n m hn hm hs ht
  have H := h z hz w hw n m hn hm ((supports_smul hc).mp hs) ((supports_smul hc).mp ht)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  calc ‖n - m‖ ≤ β * ‖z - w‖ := H
    _ = β / c * (c * ‖z - w‖) := by field_simp
end Scaling

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem hardObjective_smul (L r : ℝ) (x : Ambient ι) :
    hardObjective L r (r • x) = L * r ^ 2 * cost x := by
  have e : (embed (fun _ : ι => 0, 32 * L * r) : Ambient ι) = (L * r) • tilt := by
    rw [tilt, ← scale_embed]; congr 1; ext i <;> simp [scalePt]; ring
  simp only [hardObjective, cost, quadratic, e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

omit [LinearOrder ι] in
theorem sInf_hardObjective_smul (L r : ℝ) (hL : 0 ≤ L) (C : Set (Ambient ι)) :
    sInf (hardObjective L r '' (r • C)) = L * r ^ 2 * valC C := by
  have : hardObjective L r '' (r • C) = (L * r ^ 2) • (cost '' C) := by
    ext v; constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨cost x, ⟨x, hx, rfl⟩, by simp [hardObjective_smul, smul_eq_mul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨r • x, ⟨x, hx, rfl⟩, by simp [hardObjective_smul, smul_eq_mul]⟩
  rw [this, Real.sInf_smul_of_nonneg (by positivity), valC, smul_eq_mul]

/-- The simplex scale at prescribed parameters, `0.99 (D - 2/β) / √2`. -/
noncomputable def hardScale (β D : ℝ) : ℝ := 99 / 100 * (D - 2 / β) / Real.sqrt 2

/-- The public start point `(hardScale β D • e_a, 0)`, returned for the zero direction. -/
noncomputable def hardStart (β D : ℝ) (a : ι) : Ambient ι := embed (hardScale β D • atom a, 0)

/-- The simplex scale of the normalized family, `0.99 (βD - 2) / √2 = β · hardScale β D`. -/
noncomputable def unitScale (β D : ℝ) : ℝ := 99 / 100 * ((β * D - 2) / Real.sqrt 2)

theorem unitScale_pos {β D : ℝ} (hD : 2 < β * D) : 0 < unitScale β D := by
  have : 0 < (β * D - 2) / Real.sqrt 2 := div_pos (by linarith) (by positivity)
  unfold unitScale; positivity

omit [Fintype ι] in
theorem hardStart_eq {β D : ℝ} (hβ : 0 < β) (a : ι) :
    hardStart β D a = (1 / β) • start (unitScale β D) a := by
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [hardStart, start, ← scale_embed]; congr 1; ext i
  · simp only [scalePt, Pi.smul_apply, smul_eq_mul, hardScale, unitScale]
    field_simp
  · simp [scalePt]

/-- The normalized threshold `(βD - 2)² / (64 (T + 1))` leaves room for the jitter. -/
theorem unit_threshold {β D : ℝ} (hD : 2 < β * D) (T : ℕ) :
    (β * D - 2) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)) +
        (unitScale β D + 35) * (2 * unitScale β D + 5) * (2 * jitter (unitScale β D) T) ≤
      unitScale β D ^ 2 / (16 * ((T + 1 : ℕ) : ℝ)) := by
  set A₀ : ℝ := (β * D - 2) / Real.sqrt 2 with hA₀
  have hA₀pos : 0 < A₀ := div_pos (by linarith) (by positivity)
  set A := unitScale β D with hA_def
  have hA : 0 < A := unitScale_pos hD
  set k : ℝ := ((T + 1 : ℕ) : ℝ) with hk_def
  have hk : 0 < k := by positivity
  have S := settings hA Unit T
  have b : (A + 35) * (2 * A + 5) * (2 * jitter A T) ≤ 4 * A ^ 2 / (1000000 * k) :=
    S.2.2.2.2.2.2.1
  set U := A₀ ^ 2 / k
  have hU : 0 ≤ U := by positivity
  have hA₀sq : A₀ ^ 2 = (β * D - 2) ^ 2 / 2 := by
    rw [hA₀, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have e1 : (β * D - 2) ^ 2 / (64 * k) = U / 32 := by
    simp only [U, hA₀sq]; field_simp; ring
  have e2 : A ^ 2 / (16 * k) = 9801 / 10000 * U / 16 := by
    simp only [hA_def, unitScale, U, ← hA₀]; field_simp; ring
  have e3 : 4 * A ^ 2 / (1000000 * k) = 4 * (9801 / 10000) * U / 1000000 := by
    simp only [hA_def, unitScale, U, ← hA₀]; field_simp; ring
  rw [e1, e2]; rw [e3] at b; linarith

/-- **The rescaled instances belong to the class.** Each body `(1/β) C` of the normalized
jittered family is compact and convex with nonempty interior, diameter at most `D`, `β`-Lipschitz
unit normals and a unique minimizer in every nonzero direction; it contains `hardStart β D a`,
and its oracle is the rescaled oracle of `C`, which is measurable. -/
theorem scaled_instance {β D : ℝ} (hβ : 0 < β) (hD : 2 < β * D) (T : ℕ) (a : ι)
    (Dt : Draw ι T) {J : Finset ι} (hJ : J ∈ shells T a) :
    let C := instanceBody (unitScale β D) a T Dt (insert a J)
    IsCompact ((1 / β) • C) ∧ Convex ℝ ((1 / β) • C) ∧ (interior ((1 / β) • C)).Nonempty ∧
      Metric.diam ((1 / β) • C) ≤ D ∧ Upper.LipschitzNormals ((1 / β) • C) β ∧
      (∀ q, q ≠ 0 → ∃! x, MinAt ((1 / β) • C) q x) ∧ hardStart β D a ∈ (1 / β) • C ∧
      reply ((1 / β) • C) (hardStart β D a) =
        (fun q => (1 / β) • reply C (start (unitScale β D) a) q) ∧
      Measurable (reply ((1 / β) • C) (hardStart β D a)) := by
  intro C
  set c : ℝ := 1 / β with hc_def
  have hc : 0 < c := by positivity
  set A := unitScale β D with hA_def
  have hA : 0 < A := unitScale_pos hD
  have si := shell_info hJ
  have size : 1 < (insert a J).card := by rw [si.2]; omega
  obtain ⟨hcC, hv, inter, reg, diam, st, -, uniq, meas, -⟩ :=
    fixed_instance_spec hA a T Dt si.1 size
  have S := settings hA ι T
  have hreply : reply (c • C) (hardStart β D a) = fun q => c • reply C (start A a) q := by
    funext q; rw [hardStart_eq hβ, reply_smul hcC st hc uniq]
  refine ⟨hcC.smul c, hv.smul c, ?_, ?_, ?_, fun q hq => unique_smul hc (uniq q hq), ?_, hreply,
    ?_⟩
  · rw [interior_smul₀ hc.ne']; exact inter.smul_set
  · rw [diam_smul₀, Real.norm_eq_abs, abs_of_pos hc]
    set A₀ : ℝ := (β * D - 2) / Real.sqrt 2 with hA₀
    have hA₀pos : 0 < A₀ := div_pos (by linarith) (by positivity)
    have s2 : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
    have h2 : 2 * (2 * jitter A T) ≤ A / 1000 := S.2.2.2.2.2.2.2.1
    have e : Real.sqrt 2 * A₀ = β * D - 2 := by
      simp only [hA₀]; field_simp
    have eA : Real.sqrt 2 * A = 99 / 100 * (Real.sqrt 2 * A₀) := by
      rw [hA_def, unitScale, ← hA₀]; ring
    have h3 : 1 * A₀ ≤ Real.sqrt 2 * A₀ := mul_le_mul_of_nonneg_right s2.le hA₀pos.le
    have hAA : A = 99 / 100 * A₀ := by rw [hA_def, unitScale, ← hA₀]
    have : Metric.diam C ≤ 2 + Real.sqrt 2 * A₀ := by
      refine diam.trans ?_
      linarith
    calc c * Metric.diam C ≤ c * (2 + Real.sqrt 2 * A₀) := mul_le_mul_of_nonneg_left this hc.le
      _ = D := by rw [e, hc_def]; field_simp; ring
  · simpa [hc_def] using lipschitzNormals_smul hc reg
  · rw [hardStart_eq hβ]; exact Set.smul_mem_smul_set st
  · rw [hreply]; exact meas.const_smul c

omit [LinearOrder ι] in
/-- Failure of the normalized output `c⁻¹ z` on `C` at threshold `θ` is failure of `z` on
`c C` for the hard objective at threshold `L c² θ`. -/
theorem bad_smul {L c θ : ℝ} (hL : 0 < L) (hc : 0 < c) (C : Set (Ambient ι)) (z : Ambient ι) :
    Bad C θ (c⁻¹ • z) ↔ z ∉ c • C ∨
      L * c ^ 2 * θ ≤ hardObjective L c z - sInf (hardObjective L c '' (c • C)) := by
  have hobj : hardObjective L c z = L * c ^ 2 * cost (c⁻¹ • z) := by
    rw [← hardObjective_smul, smul_inv_smul₀ hc.ne']
  have hp : 0 < L * c ^ 2 := by positivity
  rw [Bad, Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', sInf_hardObjective_smul L c hL.le C, hobj,
    ← mul_sub]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (mul_le_mul_of_nonneg_left h hp.le)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (le_of_mul_le_mul_left h hp)

theorem prescribed_threshold {L β D : ℝ} (hβ : 0 < β) (k : ℝ) :
    L * (D - 2 / β) ^ 2 / (64 * k) = L * (1 / β) ^ 2 * ((β * D - 2) ^ 2 / (64 * k)) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  field_simp

/-- **The lower bound with unique linear minimizers, at prescribed parameters.** -/
theorem prescribed_unique_lower_bound {Ω : Type*} [MeasurableSpace Ω] (T : ℕ) (a : ι)
    (hN : Fintype.card ι = 256 * (T + 1)) {L β D : ℝ} (hL : 0 < L) (hβ : 0 < β)
    (hD : 2 < β * D) (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T)
    (hs : Method.IsMeasurable s) :
    ∃ C : Set (Ambient ι), IsCompact C ∧ Convex ℝ C ∧ (interior C).Nonempty ∧
      Metric.diam C ≤ D ∧ Upper.LipschitzNormals C β ∧ (∀ q, q ≠ 0 → ∃! x, MinAt C q x) ∧
      hardStart β D a ∈ C ∧ (∀ q, MinAt C q (reply C (hardStart β D a) q)) ∧
      1 / 5 ≤ μ.real {ω | (s ω).run (reply C (hardStart β D a)) ∉ C ∨
        L * (D - 2 / β) ^ 2 / (64 * ((T + 1 : ℕ) : ℝ)) ≤
          hardObjective L (1 / β) ((s ω).run (reply C (hardStart β D a))) -
            sInf (hardObjective L (1 / β) '' C)} := by
  set c : ℝ := 1 / β with hc_def
  have hc : 0 < c := by positivity
  set A := unitScale β D
  have hA : 0 < A := unitScale_pos hD
  let s' : Ω → Method (Ambient ι) T := fun ω => (s ω).simulate c
  have hs' : Method.IsMeasurable s' := by
    intro O hO
    have h1 := (hs (fun q => c • O q) (hO.const_smul c)).const_smul c⁻¹
    convert h1 using 1
    funext ω
    exact Method.simulate_run_eq (s ω) c O
  obtain ⟨Dt, J, hJ, -, -, -, -, -, -, -, -, -, prob⟩ :=
    unique_lmo_lower_bound hA a T hN (unit_threshold hD T) μ s' hs'
  obtain ⟨hcC, hv, inter, diam, reg, uniq, st, hreply, -⟩ := scaled_instance hβ hD T a Dt hJ
  set C := instanceBody A a T Dt (insert a J)
  refine ⟨c • C, hcC, hv, inter, diam, reg, uniq, st,
    fun q => reply_min hcC st q, prob.trans (le_of_eq (congrArg μ.real (Set.ext fun ω => ?_)))⟩
  have run : (s' ω).run (reply C (start A a)) =
      c⁻¹ • (s ω).run (reply (c • C) (hardStart β D a)) := by
    have e : reply (c • C) (hardStart β D a) = fun q => c • reply C (start A a) q := hreply
    simp only [s', Method.simulate_run_eq, e]
  simp only [Set.mem_ofPred_eq, run, prescribed_threshold hβ]
  exact bad_smul hL hc C _

end Lemmata.FrankWolfePS.Unique
