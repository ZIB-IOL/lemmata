module
public import Lemmata.FrankWolfePS.Joint.Main
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace Gradient NNReal Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]

noncomputable def iterationCount (H ε θ : ℝ) : ℕ := ⌈Real.log (H / ε) / θ⌉₊

theorem geometric_tolerance {H ε θ : ℝ} (hH : 0 ≤ H) (he : 0 < ε) (ht : 0 < θ) (ht1 : θ ≤ 1) :
    (1 - θ) ^ (iterationCount H ε θ) * H ≤ ε := by
  by_cases zero : H = 0
  · simp [zero, he.le]
  have hp : 0 < H := lt_of_le_of_ne hH (Ne.symm zero)
  let n := iterationCount H ε θ
  have ceil : Real.log (H / ε) / θ ≤ (n : ℝ) := Nat.le_ceil _
  have length := (div_le_iff₀ ht).mp ceil
  have E := Real.exp_le_exp.mpr (show (n : ℝ) * (-θ) ≤ -Real.log (H / ε) by linarith)
  rw [Real.exp_nat_mul, Real.exp_neg (Real.log _), Real.exp_log (div_pos hp he)] at E
  have small := (pow_le_pow_left₀ (sub_nonneg.mpr ht1) (Real.one_sub_le_exp_neg θ) n).trans E
  apply (mul_le_mul_of_nonneg_right small hH).trans
  exact le_of_eq (by field_simp)

theorem joint_body_linear_tolerance {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r R μ ε : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (innerBall : InnerBall C r) (outer : OuterBall C R)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hμ : 0 < μ) (df : Differentiable ℝ f)
    (sc : StrongConvexOn Set.univ μ f) (smooth : LipschitzWith L (∇ f)) (he : 0 < ε)
    (ball : Bool) (cert : ball = true → R = r) {x₀ : E} (hx : x₀ ∈ C) :
    let H := (L : ℝ) / 2 * (Metric.diam C) ^ 2
    let θ := share r R * (μ / L)
    let n := iterationCount H ε θ
    let ans := projectedGradientRun O (∇ f) L r ball x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
      ∀ w ∈ C, f ans.1 - f w ≤ ε := by
  dsimp only
  let H := (L : ℝ) / 2 * (Metric.diam C) ^ 2
  let θ := share r R * (μ / L)
  let n := iterationCount H ε θ
  obtain ⟨hm, oc, gc, rate⟩ :=
      joint_body_linear_upper hc cv hr hR innerBall outer O hμ df sc smooth ball cert hx n
  obtain ⟨_, _, hLμ⟩ := analytic_parameters hμ df sc smooth C
  have hL := hμ.trans_le hLμ
  have c := share_bounds hr hR
  refine ⟨hm, oc, gc, fun w hw => (rate w hw).trans ?_⟩
  exact geometric_tolerance (by dsimp [H]; positivity) he (mul_pos c.1 (div_pos hμ hL))
    (by linarith [factor_nonneg hμ hLμ c.2])

/-- If the quadratic center is public, the gradient expression is local
arithmetic. Only body-oracle evaluations are charged. -/
noncomputable def disclosedJointRun {C : Set E} (O : LMO C) (u : E) (L r : ℝ)
    (ball : Bool) (x₀ : E) (n : ℕ) : E × ℕ × ℕ :=
  let ans := projectedGradientRun O (isoGrad L u) L r ball x₀ n
  (ans.1, ans.2.1, 0)

theorem disclosed_joint_quadratic {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r R L : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (innerBall : InnerBall C r) (outer : OuterBall C R)
    (O : LMO C) (u : E) (hL : 0 < L) (ball : Bool) (cert : ball = true → R = r)
    {x₀ : E} (hx : x₀ ∈ C) (n : ℕ) :
    let ans := disclosedJointRun O u L r ball x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 = 0 ∧
    ∀ w ∈ C, iso L u ans.1 - iso L u w ≤ (1 - share r R) ^ n * (L / 2 * (Metric.diam C) ^ 2) := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have eq := parallel_of_normals hc cv ⟨_, hx⟩ hr (normals_of_inner hr.le innerBall) he
  have mdl : Models C (iso L u) (isoGrad L u) L := by
    constructor
    · intro x _ y _
      rw [iso_taylor L u x y]
      linarith [mul_nonneg (by positivity : 0 ≤ L / 2) (_root_.sq_nonneg ‖y - x‖)]
    · intro x _ y _; exact (iso_taylor L u x y).le
  have low : StrongLower C (iso L u) (isoGrad L u) L := fun x _ y _ => (iso_taylor L u x y).ge
  obtain ⟨hm, oc, _, rate⟩ :=
      linear_of_parallel_rep eq (erosion_compact_convex hc cv hr.le).2 hc cv hr hR
    outer O mdl low hL le_rfl ball cert hx n
  refine ⟨hm, oc, rfl, ?_⟩
  simpa [disclosedJointRun, div_self hL.ne'] using rate

end Lemmata.FrankWolfePS.Joint
