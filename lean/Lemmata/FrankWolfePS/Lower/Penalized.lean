module

public import Lemmata.FrankWolfePS.Lower.Results
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-!
# A distance penalty for infeasible outputs

Grimmer and Liu measure an output `x` by `f(x) - f⋆ + ρ dist(x, C)`. If the weight `ρ` exceeds
the Lipschitz constant of the hard objective on the body by `L a`, the penalized error at a light
output (guessed mass at most `3/4`) is at least `L a² / (128 k)`. Compare `x` with its nearest
point `v` of the body: convexity of the objective at `v` leaves `f(v) - f⋆ + L a ‖x - v‖`. If `x`
is far from the body the penalty pays; otherwise `v` is nearly as light as `x`, and the height
argument applies to `v`. The light event has prior probability at least `1/4` for every tape, so
no feasibility assumption is needed.
-/

namespace Lemmata.FrankWolfePS
open Finset MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise ENNReal

section Normalized
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem norm_embed_sq (z : Pt ι) : ‖embed z‖ ^ 2 = sq z.1 + z.2 ^ 2 := by
  have h0 : (embed ((fun _ => 0, 0) : Pt ι)) = 0 := by ext i; cases i <;> rfl
  simpa [h0] using embed_dist_sq z ((fun _ => 0, 0) : Pt ι)

omit [DecidableEq ι] in
/-- Points of the normalized body have norm at most `1 + 2R`. -/
theorem norm_le_of_rounded {R : ℝ} (hR : 0 ≤ R) {I : Finset ι} {v : Ambient ι}
    (hv : v ∈ Rounded (core R I) R) : ‖v‖ ≤ 1 + 2 * R := by
  obtain ⟨_, ⟨b, hb, rfl⟩, hd⟩ := hv
  have hu : ‖embed (b, R)‖ ≤ 1 + R := by
    have e := norm_embed_sq (b, R)
    have s1 := sq_base_le_one hb
    have n0 := norm_nonneg (embed (b, R))
    nlinarith
  have h := norm_add_le (v - embed (b, R)) (embed (b, R))
  rw [sub_add_cancel] at h
  linarith

/-- **The penalized error at a light point, normalized.** If the guessed mass of `z` on `I` is at
most `3/4` and `ρ ≥ 2 + 34 R`, then `obj z - opt + ρ dist(z, C) ≥ 1 / (128 k)`. -/
theorem penalized_light {R ρ : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) {I : Finset ι}
    (hI : I.card = 8 * k) (hρ : 2 + 34 * R ≤ ρ) {z : Pt ι}
    (hm : ∑ i ∈ I, guess k z i ≤ 3 / 4) :
    1 / (128 * (k : ℝ)) ≤
      obj R z - optimum R I + ρ * Metric.infDist (embed z) (Rounded (core R I) R) := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcC := (body_compact_convex I R).1
  obtain ⟨i, hi⟩ : I.Nonempty := card_pos.mp (by omega)
  have hne : (Rounded (core R I) R).Nonempty :=
    ⟨_, ⟨_, ⟨atom i, atom_base hi, rfl⟩, by rw [sub_self, norm_zero]; exact hR.le⟩⟩
  obtain ⟨v, hv, hd⟩ := hcC.exists_infDist_eq_dist hne (embed z)
  obtain ⟨w, hw⟩ : ∃ w : Pt ι, w = coords v := ⟨_, rfl⟩
  have hvw : embed w = v := by rw [hw, embed_coords]
  have hwf : Feasible R I w := (feasible_iff_rounded hR I _).mpr (by rw [hvw]; exact hv)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ‖embed z - v‖ := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := hδ ▸ norm_nonneg _
  have hdist : Metric.infDist (embed z) (Rounded (core R I) R) = δ := by
    rw [hd, dist_eq_norm, hδ]
  -- convexity of the objective at the nearest point
  have taylor : obj R w - (1 + 34 * R) * δ ≤ obj R z := by
    have e1 := objective_as_quadratic 1 R z
    have e2 := objective_as_quadratic 1 R w
    have t := quadratic_taylor 1 (embed (fun _ : ι => 0, 32 * 1 * R)) (embed w) (embed z)
    rw [hvw] at e2 t
    rw [one_mul] at e1 e2
    rw [← hδ] at t
    have cs := neg_le_of_abs_le
      (abs_real_inner_le_norm (grad 1 (embed (fun _ : ι => 0, 32 * 1 * R)) v) (embed z - v))
    rw [← hδ] at cs
    have hc : ‖(embed (fun _ : ι => 0, 32 * 1 * R) : Ambient ι)‖ ≤ 32 * R := by
      have e := norm_embed_sq ((fun _ : ι => 0, 32 * 1 * R) : Pt ι)
      have s0 : sq (fun _ : ι => (0 : ℝ)) = 0 := by simp [sq]
      rw [s0, zero_add] at e
      have n0 := norm_nonneg (embed ((fun _ : ι => 0, 32 * 1 * R) : Pt ι))
      nlinarith
    have ng : ‖grad 1 (embed (fun _ : ι => 0, 32 * 1 * R)) v‖ ≤ 1 + 34 * R := by
      have h := norm_add_le v (embed ((fun _ : ι => 0, 32 * 1 * R) : Pt ι))
      simp only [grad, one_smul]
      linarith [norm_le_of_rounded hR.le hv]
    have sq0 : 0 ≤ (1 / 2 : ℝ) * δ ^ 2 := by positivity
    have prod := mul_le_mul_of_nonneg_right ng hδ0
    calc obj R w - (1 + 34 * R) * δ
        ≤ obj R w - ‖grad 1 (embed (fun _ : ι => 0, 32 * 1 * R)) v‖ * δ := by linarith
      _ ≤ obj R w + ⟪grad 1 (embed (fun _ : ι => 0, 32 * 1 * R)) v, embed z - v⟫ := by linarith
      _ ≤ obj R w + ⟪grad 1 (embed (fun _ : ι => 0, 32 * 1 * R)) v, embed z - v⟫ +
          1 / 2 * δ ^ 2 := by linarith
      _ = obj R z := by rw [e1, e2, t]
  have opt_le : optimum R I ≤ obj R w := csInf_le (objective_bddBelow hR I) ⟨w, hwf, rfl⟩
  have hb := barycenter_upper hR hk hI
  have base : obj R w - optimum R I + δ ≤
      obj R z - optimum R I + ρ * Metric.infDist (embed z) (Rounded (core R I) R) := by
    rw [hdist]; nlinarith [mul_le_mul_of_nonneg_right hρ hδ0]
  by_cases far : 1 / (128 * (k : ℝ)) ≤ δ
  · linarith
  push Not at far
  have hδk : (k : ℝ) * δ ^ 2 ≤ 1 / 16384 := by
    have h1 : δ * (128 * k) < 1 := by rwa [lt_div_iff₀ (by positivity)] at far
    have h0 : 0 ≤ δ * (128 * k) := by positivity
    have h2 : (δ * (128 * k)) ^ 2 ≤ 1 := by nlinarith
    have h3 : (k : ℝ) * δ ^ 2 * (16384 * k) ≤ 1 := by linarith
    have h4 : 0 ≤ (k : ℝ) * δ ^ 2 := by positivity
    have h5 := mul_le_mul_of_nonneg_left hk1 h4
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hzw : sq (fun i => z.1 i - w.1 i) ≤ δ ^ 2 := by
    have := embed_dist_sq z w
    rw [hvw, ← hδ] at this
    nlinarith [_root_.sq_nonneg (z.2 - w.2)]
  by_cases small : 4 * (k : ℝ) * sq z.1 ≤ 1
  · have hz : ∑ i ∈ I, |z.1 i| ≤ 3 / 4 := by simpa [guess, small] using hm
    have sub : ∑ i ∈ I, |w.1 i - z.1 i| ^ 2 ≤ sq (fun i => z.1 i - w.1 i) := by
      simp only [sq_abs, sq, ← sub_sq_comm (w.1 _) (z.1 _)]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => _root_.sq_nonneg _
    have cs := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i => |w.1 i - z.1 i|)
    have hcard : (I.card : ℝ) = 8 * k := by exact_mod_cast hI
    rw [hcard] at cs
    have e0 : 0 ≤ ∑ i ∈ I, |w.1 i - z.1 i| := sum_nonneg fun i _ => abs_nonneg _
    have b1 := mul_le_mul_of_nonneg_left (sub.trans hzw) (by positivity : (0 : ℝ) ≤ 8 * k)
    have e2 : (∑ i ∈ I, |w.1 i - z.1 i|) ^ 2 ≤ 1 / 2048 := by linarith
    have e1 : ∑ i ∈ I, |w.1 i - z.1 i| ≤ 1 / 20 := by nlinarith
    have hw_mass : ∑ i ∈ I, w.1 i ≤ 4 / 5 := by
      have each : ∀ i ∈ I, w.1 i ≤ |z.1 i| + |w.1 i - z.1 i| := fun i _ => by
        have h1 := le_abs_self (w.1 i)
        have h2 := abs_sub_abs_le_abs_sub (w.1 i) (z.1 i)
        linarith
      have := sum_le_sum each
      rw [sum_add_distrib] at this
      linarith
    have hc := height_cost hk hI hwf hw_mass (by norm_num)
    have e : 2 * (1 - 4 / 5 : ℝ) ^ 2 / k = 2 / (25 * k) := by field_simp; norm_num
    rw [e] at hc
    have target : 1 / (128 * (k : ℝ)) ≤ 2 / (25 * k) - 1 / (16 * k) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith
  · push Not at small
    have young : 4 * sq z.1 ≤ 7 * sq w.1 + 28 / 3 * sq (fun i => z.1 i - w.1 i) := by
      unfold sq
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_le_sum fun i _ => by nlinarith [_root_.sq_nonneg (3 * w.1 i - 4 * (z.1 i - w.1 i))]
    have a1 := mul_le_mul_of_nonneg_left young hk'.le
    have a2 := mul_le_mul_of_nonneg_left hzw hk'.le
    have hw_big : 9 / 64 ≤ (k : ℝ) * sq w.1 := by linarith
    have hcost := (horizontal_cost hR hwf).2
    have a3 := mul_le_mul_of_nonneg_left hcost hk'.le
    have target : 1 / (128 * (k : ℝ)) ≤ 9 / (128 * k) - 1 / (16 * k) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have hw9 : 9 / (128 * (k : ℝ)) ≤ obj R w := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

end Normalized

section Physical
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {Ω : Type*} [MeasurableSpace Ω]

/-- The penalized error of a point for the body `physicalBody a r I`: the gap of the hard
objective plus `ρ` times the distance to the body. -/
noncomputable def physicalPenalized (L a r ρ : ℝ) (I : Finset ι) (x : Ambient ι) : ℝ :=
  hardObjective L r x - sInf (hardObjective L r '' physicalBody a r I) +
    ρ * Metric.infDist x (physicalBody a r I)

omit [LinearOrder ι] in
theorem physicalPenalized_continuous (L a r ρ : ℝ) (I : Finset ι) :
    Continuous (physicalPenalized L a r ρ I) :=
  ((hardObjective_continuous L r).sub continuous_const).add
    (continuous_const.mul (Metric.continuous_infDist_pt _))

/-- The penalized error in normalized coordinates. -/
theorem physicalPenalized_scale {L a r ρ : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r)
    {I : Finset ι} (hne : I.Nonempty) (z : Pt ι) :
    physicalPenalized L a r ρ I (a • embed z) = L * a ^ 2 * (obj (r / a) z - optimum (r / a) I +
      ρ / (L * a) * Metric.infDist (embed z) (Rounded (core (r / a) I) (r / a))) := by
  rw [physicalPenalized, ← physicalOpt_eq_sInf, physicalOpt_eq hL ha hr hne, physicalBody,
    infDist_smul₀ ha.ne', Real.norm_eq_abs, abs_of_pos ha, hardObjective_coords, ← scale_embed,
    coords_embed, obj_scale a r ha]
  have hL0 := hL.ne'
  have ha0 := ha.ne'
  field_simp

/-- **Penalized error on the hard family.** For a weight `ρ ≥ L (2a + 34 r)` and every randomized
method requiring no more than `T` calls with measurable returns, some instance, chosen before the
tape, has penalized error at least `L a² / (128 (T + 1))` with probability at least `1/4`; the
mean of the penalized error, in `[0, ∞]`, is at least a quarter of that. -/
theorem penalized_lower_bound (T : ℕ) (anchor : ι) (hN : Fintype.card ι = 256 * (T + 1))
    {L a r ρ : ℝ} (hL : 0 < L) (ha : 0 < a) (hr : 0 < r) (hρ : L * (2 * a + 34 * r) ≤ ρ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → Method (Ambient ι) T)
    (meas : ∀ S ∈ instanceSets T anchor,
      Measurable fun ω => (s ω).run (physOracle a r anchor (insert anchor S))) :
    ∃ S ∈ instanceSets T anchor, let I := insert anchor S
      1 / 4 ≤ μ.real {ω | L * a ^ 2 / (128 * ((T + 1 : ℕ) : ℝ)) ≤
        physicalPenalized L a r ρ I ((s ω).run (physOracle a r anchor I))} ∧
      ENNReal.ofReal (L * a ^ 2 / (512 * ((T + 1 : ℕ) : ℝ))) ≤
        ∫⁻ ω, ENNReal.ofReal
          (physicalPenalized L a r ρ I ((s ω).run (physOracle a r anchor I))) ∂μ := by
  classical
  set k := T + 1 with hk_def
  have hk : 0 < k := Nat.succ_pos T
  have hR : 0 < r / a := div_pos hr ha
  set thr := L * a ^ 2 / (128 * (k : ℝ)) with hthr
  have hρ' : 2 + 34 * (r / a) ≤ ρ / (L * a) := by
    rw [le_div_iff₀ (by positivity)]
    have e : (2 + 34 * (r / a)) * (L * a) = L * (2 * a + 34 * r) := by field_simp
    linarith
  let F := fun (I : Finset ι) (z : Pt ι) => thr ≤ physicalPenalized L a r ρ I (a • embed z)
  have hF : ∀ I z, I.card = 8 * k → ∑ i ∈ I, guess k z i ≤ 3 / 4 → F I z := by
    intro I z hI hm
    obtain ⟨i, hi⟩ : I.Nonempty := card_pos.mp (by omega)
    have P := penalized_light hR hk hI hρ' hm
    change thr ≤ physicalPenalized L a r ρ I (a • embed z)
    rw [physicalPenalized_scale hL ha hr ⟨i, hi⟩, hthr]
    have e : L * a ^ 2 / (128 * (k : ℝ)) = L * a ^ 2 * (1 / (128 * (k : ℝ))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left P (by positivity)
  let e := fun S => {ω | thr ≤ physicalPenalized L a r ρ (insert anchor S)
    ((s ω).run (physOracle a r anchor (insert anchor S)))}
  have back (ω : Ω) (I : Finset ι) :
      a • embed ((((s ω).simulate a).orders (r / a) anchor).run I) =
        (s ω).run (physOracle a r anchor I) := by
    rw [Method.orders_run, Method.simulate_run, ← scale_embed, scale_scale,
      mul_inv_cancel₀ ha.ne', scale_one, embed_coords]
  have fixed (ω : Ω) :
      ((instanceSets T anchor).card : ℝ) * (1 / 4) ≤
        ∑ S ∈ instanceSets T anchor, flag (ω ∈ e S) := by
    have H := fixed_tape_mass T anchor hN F hF (((s ω).simulate a).orders (r / a) anchor)
    rw [mul_one_div]
    refine H.trans (le_of_eq (sum_congr rfl fun S _ => ?_))
    simp only [F, e, Set.mem_ofPred_eq, back]
  have ne : (instanceSets T anchor).Nonempty := by
    apply powersetCard_nonempty.mpr
    simp [hN]
    omega
  have me (S : Finset ι) (hS : S ∈ instanceSets T anchor) : MeasurableSet (e S) :=
    measurableSet_le measurable_const
      ((physicalPenalized_continuous L a r ρ _).measurable.comp (meas S hS))
  obtain ⟨S, hS, hp⟩ := select_tape _ ne μ (1 / 4) e me fixed
  refine ⟨S, hS, hp, ?_⟩
  have fm : Measurable fun ω => ENNReal.ofReal (physicalPenalized L a r ρ (insert anchor S)
      ((s ω).run (physOracle a r anchor (insert anchor S)))) :=
    ENNReal.measurable_ofReal.comp
      ((physicalPenalized_continuous L a r ρ _).measurable.comp (meas S hS))
  have mk := mul_meas_ge_le_lintegral₀ (μ := μ) fm.aemeasurable (ENNReal.ofReal thr)
  have sub : e S ⊆ {ω | ENNReal.ofReal thr ≤ ENNReal.ofReal (physicalPenalized L a r ρ
      (insert anchor S) ((s ω).run (physOracle a r anchor (insert anchor S))))} :=
    fun ω h => ENNReal.ofReal_le_ofReal h
  have hq : ENNReal.ofReal (1 / 4) ≤ μ (e S) := ENNReal.ofReal_le_of_le_toReal hp
  have hthr0 : 0 ≤ thr := by positivity
  calc ENNReal.ofReal (L * a ^ 2 / (512 * (k : ℝ)))
      = ENNReal.ofReal thr * ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_mul hthr0, hthr]; congr 1; ring
    _ ≤ ENNReal.ofReal thr * μ (e S) := by gcongr
    _ ≤ ENNReal.ofReal thr * μ {ω | ENNReal.ofReal thr ≤ ENNReal.ofReal (physicalPenalized L a r ρ
          (insert anchor S) ((s ω).run (physOracle a r anchor (insert anchor S))))} := by
        gcongr
    _ ≤ _ := mk

end Physical

end Lemmata.FrankWolfePS
