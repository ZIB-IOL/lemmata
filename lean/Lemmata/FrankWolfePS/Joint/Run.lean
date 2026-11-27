module
public import Lemmata.FrankWolfePS.Joint.Step
public import Lemmata.FrankWolfePS.Joint.Objective
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Each loop step evaluates one gradient at the stored point and adds the
actual number of body LMOs returned by modelStep. -/
noncomputable def projectedGradientLoop {C : Set E} (O : LMO C) (g : E → E) (L r : ℝ) (ball : Bool)
    (p : E × E) : ℕ → (E × E) × ℕ × ℕ
  | 0 => (p, 0, 0)
  | n + 1 => let prev := projectedGradientLoop O g L r ball p n
           let x := prev.1.2
           let v := modelStep O ball r (target L (g x) x) prev.1.1
           (v.1, prev.2.1 + v.2, prev.2.2 + 1)

theorem factor_nonneg {c μ L : ℝ} (hμ : 0 < μ) (hLμ : μ ≤ L) (hc : c ≤ 1) :
    0 ≤ 1 - c * (μ / L) := by
  have hL := hμ.trans_le hLμ
  have h := mul_le_mul_of_nonneg_right hc (div_nonneg hμ.le hL.le)
  linarith [(div_le_one hL).mpr hLμ]

theorem loop_bound {K : Set E} (conv : Convex ℝ K) (bodyConv : Convex ℝ (Rounded K r))
    (O : LMO (Rounded K r)) {f : E → ℝ} {g : E → E} {L μ c : ℝ} {ball : Bool}
    (mdl : Models (Rounded K r) f g L) (strong : StrongLower (Rounded K r) f g μ)
    (hr : 0 < r) (hμ : 0 < μ) (hLμ : μ ≤ L) (hc : 0 ≤ c) (hc1 : c ≤ 1) (reg : Regime K r c ball)
    {p : E × E} (hp : StateOK K r p) (n : ℕ) :
    let ans := projectedGradientLoop O g L r ball p n
    StateOK K r ans.1 ∧ ans.2.1 ≤ n * (if ball then 0 else 1) ∧ ans.2.2 = n ∧
    ∀ w ∈ Rounded K r, f ans.1.2 - f w ≤ (1 - c * (μ / L)) ^ n * (f p.2 - f w) := by
  induction n with
  | zero => simp [projectedGradientLoop, hp]
  | succ n ih =>
    obtain ⟨mem, calls, grads, rate⟩ := ih
    let prev := projectedGradientLoop O g L r ball p n
    let u := target L (g prev.1.2) prev.1.2
    let v := modelStep O ball r u prev.1.1
    obtain ⟨hm, hc', hmul⟩ := model_step_spec conv O hr hc hc1 reg u mem
    have next := objective_step bodyConv mdl strong hμ hLμ hc (state_mem mem) (state_mem hm) hmul
    refine ⟨hm, ?_, by simp only [projectedGradientLoop, grads], fun w hw => ?_⟩
    · change prev.2.1 + v.2 ≤ (n + 1) * _
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add calls hc'
    · change f v.1.2 - f w ≤ _
      exact (next w hw).trans (by
        rw [pow_succ]
        linarith only [mul_le_mul_of_nonneg_left (rate w hw) (factor_nonneg hμ hLμ hc1)])

noncomputable def projectedGradientRun {C : Set E} (O : LMO C) (g : E → E) (L r : ℝ) (ball : Bool)
    (x₀ : E) (n : ℕ) : E × ℕ × ℕ :=
  let q := g x₀
  if q = 0 then (x₀, 0, 1)
  else let s := O.query q
       let a := s + r • unit q
       let v := projectedGradientLoop O g L r ball (a, s) n
       (v.1.2, 1 + v.2.1, 1 + v.2.2)

theorem initialization {C : Set E} {f : E → ℝ} {g : E → E} {L D : ℝ}
    (mdl : Models C f g L) (hL : 0 ≤ L) (O : LMO C) {x : E} (hx : x ∈ C)
    (width : ∀ y ∈ C, ‖y - x‖ ≤ D) : ∀ w ∈ C, f (O.query (g x)) - f w ≤ L / 2 * D ^ 2 := by
  intro w hw
  have U := mdl.upper x hx _ (O.mem (g x))
  have B := mdl.lower x hx w hw
  rw [inner_sub_right] at U B
  have W := pow_le_pow_left₀ (norm_nonneg _) (width _ (O.mem (g x))) 2
  linarith only [U, B, O.least (g x) w hw, mul_le_mul_of_nonneg_left W (by positivity : 0 ≤ L / 2)]

theorem initial_state {K : Set E} {r : ℝ} (hr : 0 < r) (O : LMO (Rounded K r))
    {q : E} (ne : q ≠ 0) : StateOK K r (unwrap O r q, O.query q) := by
  refine ⟨(unwrap_spec hr O ne).1, ?_⟩
  change ‖O.query q - (O.query q + r • unit q)‖ ≤ r
  simp [norm_smul, abs_of_pos hr, norm_unit ne]

theorem parallel_linear_upper {K : Set E} (conv : Convex ℝ K) (bodyConv : Convex ℝ (Rounded K r))
    (O : LMO (Rounded K r)) {f : E → ℝ} {g : E → E} {L μ c D : ℝ} {ball : Bool}
    (mdl : Models (Rounded K r) f g L) (strong : StrongLower (Rounded K r) f g μ)
    (hr : 0 < r) (hμ : 0 < μ) (hLμ : μ ≤ L) (hc : 0 ≤ c) (hc1 : c ≤ 1) (reg : Regime K r c ball)
    {x₀ : E} (hx : x₀ ∈ Rounded K r) (width : ∀ y ∈ Rounded K r, ‖y - x₀‖ ≤ D) (n : ℕ) :
    let ans := projectedGradientRun O g L r ball x₀ n
    ans.1 ∈ Rounded K r ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
    ∀ w ∈ Rounded K r, f ans.1 - f w ≤ (1 - c * (μ / L)) ^ n * (L / 2 * D ^ 2) := by
  have hL := hμ.trans_le hLμ
  have factor := factor_nonneg hμ hLμ hc1
  by_cases zero : g x₀ = 0
  · simp only [projectedGradientRun, zero, ite_true]
    refine ⟨hx, Nat.zero_le _, by omega, fun w hw => ?_⟩
    have B := mdl.lower x₀ hx w hw
    rw [zero, inner_zero_left, add_zero] at B
    exact (sub_nonpos.mpr B).trans (mul_nonneg (pow_nonneg factor n) (by positivity))
  · let q := g x₀
    let a := unwrap O r q
    let s := O.query q
    have init : StateOK K r (a, s) := initial_state hr O zero
    obtain ⟨mem, oc, gc, rate⟩ := loop_bound conv bodyConv O mdl strong hr hμ hLμ hc hc1 reg init n
    simp only [projectedGradientRun, zero, ite_false]
    refine ⟨state_mem mem, Nat.add_le_add_left oc _, Nat.add_le_add_left gc.le 1, fun w hw => ?_⟩
    have warm := initialization mdl hL.le O hx width w hw
    exact (rate w hw).trans (mul_le_mul_of_nonneg_left warm (pow_nonneg factor n))

end Lemmata.FrankWolfePS.Joint
