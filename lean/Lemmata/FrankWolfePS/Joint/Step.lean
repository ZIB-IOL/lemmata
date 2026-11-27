module
public import Lemmata.FrankWolfePS.Joint.Model
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A state stores the core center and the current feasible point; their
difference is the available ball component. -/
def StateOK (K : Set E) (r : ℝ) (p : E × E) := p.1 ∈ K ∧ ‖p.2 - p.1‖ ≤ r

omit [InnerProductSpace ℝ E] in
theorem state_mem {K : Set E} {r : ℝ} {p : E × E} (hp : StateOK K r p) :
    p.2 ∈ Rounded K r := ⟨p.1, hp.1, hp.2⟩

noncomputable def projected (r : ℝ) (u a : E) := (a, liftInner r u a)

theorem projected_ok {K : Set E} {r : ℝ} (hr : 0 ≤ r) {a : E} (ha : a ∈ K) (u : E) :
    StateOK K r (projected r u a) :=
  ⟨ha, by simpa [projected, liftInner] using norm_clip hr (u - a)⟩

/-- The boolean enables a projection-only optimization for a known ball.
The remaining inputs are public or actually queried. The integer counts body calls. -/
noncomputable def modelStep {C : Set E} (O : LMO C) (ball : Bool) (r : ℝ) (u a : E) :
    (E × E) × ℕ :=
  if ‖a - u‖ ≤ r then (projected r u a, 0)
  else if ball then (projected r u a, 0)
  else let s := unwrap O r (a - u)
       (projected r u (coreMove u a s), 1)

def Regime (K : Set E) (r c : ℝ) (ball : Bool) : Prop :=
  (∀ a ∈ K, ∀ v ∈ K, a = v) ∨
  (ball = false ∧ ∃ h, 0 < h ∧ OuterBall K h ∧ c ≤ 1 / 2 ∧ 4 * h * c ≤ r)

theorem model_step_spec {K : Set E} (conv : Convex ℝ K) (O : LMO (Rounded K r))
    {ball : Bool} {c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (hc1 : c ≤ 1) (reg : Regime K r c ball)
    (u : E) {p : E × E} (hp : StateOK K r p) :
    let ans := modelStep O ball r u p.1
    StateOK K r ans.1 ∧ ans.2 ≤ (if ball then 0 else 1) ∧
      ∀ z ∈ Rounded K r, ‖ans.1.2 - u‖ ^ 2 ≤ (1 - c) * ‖p.2 - u‖ ^ 2 + c * ‖z - u‖ ^ 2 := by
  dsimp only
  by_cases inside : ‖p.1 - u‖ ≤ r
  · simp only [modelStep, ite_eq_left inside]
    refine ⟨projected_ok hr.le hp.1 u, Nat.zero_le _, fun z _ => ?_⟩
    change ‖liftInner r u p.1 - u‖ ^ 2 ≤ _
    rw [lift_distance hr.le, max_eq_left (sub_nonpos.mpr inside), zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have q0 : p.1 - u ≠ 0 := norm_pos_iff.mp (hr.trans (lt_of_not_ge inside))
    let s := unwrap O r (p.1 - u)
    have S := unwrap_spec hr O q0
    let a' := if ball then p.1 else coreMove u p.1 s
    have rule : a' ∈ K ∧ ∀ v ∈ K, ‖a' - u‖ ^ 2 ≤ (1 - c) * ‖p.1 - u‖ ^ 2 + c * ‖v - u‖ ^ 2 := by
      rcases reg with singleton | ⟨flag, h, hh, outer, c1, small⟩
      · have same : s = p.1 := singleton _ S.1 _ hp.1
        have id : coreMove u p.1 s = p.1 := by
          rw [same, coreMove, blend, ← add_smul, sub_add_cancel, one_smul]
        have eq : a' = p.1 := by simp [a', id]
        refine ⟨eq ▸ hp.1, fun v hv => ?_⟩
        rw [eq, singleton v hv _ hp.1]; linarith only
      · subst ball
        exact core_move_model conv hr.le hh outer hc c1 small hp.1 S.1 (lt_of_not_ge inside) S.2
    have mem := projected_ok hr.le rule.1 u
    have bound (z : E) (hz : z ∈ Rounded K r) :
        ‖(projected r u a').2 - u‖ ^ 2 ≤ (1 - c) * ‖p.2 - u‖ ^ 2 + c * ‖z - u‖ ^ 2 := by
      obtain ⟨v, hv, hz'⟩ := hz
      exact lift_contraction hr.le hc hc1 hp.2 hz' (rule.2 v hv)
    have result (cost : ℕ) : StateOK K r (projected r u a') ∧ cost ≤ cost ∧
        ∀ z ∈ Rounded K r, ‖(projected r u a').2 - u‖ ^ 2 ≤ (1 - c) * ‖p.2 - u‖ ^ 2 +
            c * ‖z - u‖ ^ 2 :=
      ⟨mem, le_rfl, bound⟩
    cases ball
    · simpa [modelStep, inside, a', s] using result 1
    · simpa [modelStep, inside, a', s] using result 0

end Lemmata.FrankWolfePS.Joint
