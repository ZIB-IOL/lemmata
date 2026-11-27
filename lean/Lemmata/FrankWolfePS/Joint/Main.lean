module
public import Lemmata.FrankWolfePS.Joint.Run
public import Lemmata.FrankWolfePS.Joint.Chord
@[expose] public section
namespace Lemmata.FrankWolfePS.Joint
open Upper
open scoped RealInnerProductSpace Gradient NNReal Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] [Nontrivial E]

noncomputable def share (r R : ℝ) := if R = r then 1 else rateShare r (R - r)

theorem share_bounds {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : 0 < share r R ∧ share r R ≤ 1 := by
  by_cases eq : R = r
  · simp [share, eq]
  · have H := share_spec hr (sub_pos.mpr (lt_of_le_of_ne hR (Ne.symm eq)))
    exact ⟨by simpa [share, eq] using H.1, by rw [share, ite_eq_right eq]; linarith [H.2.1]⟩

omit [ProperSpace E] [Nontrivial E] in
theorem equal_radii_center {C K : Set E} {r : ℝ} (rep : C = Rounded K r) (hr : 0 < r)
    (outer : OuterBall C r) (O : LMO C) (e : E) (he : e ≠ 0) :
    K = {unwrap O r e} ∧ C = Metric.closedBall (unwrap O r e) r := by
  subst C
  have H : OuterBall K 0 := by simpa using core_outer hr.le (le_refl r) outer
  have S := unwrap_spec hr O he
  have singleton := core_singleton H S.1 he S.2
  have eq : K = {unwrap O r e} := by
    ext a
    exact ⟨singleton a, fun h => (show a = unwrap O r e from h) ▸ S.1⟩
  refine ⟨eq, ?_⟩
  ext a
  constructor
  · rintro ⟨s, hs, hd⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, singleton s hs] using hd
  · intro h
    exact ⟨_, S.1, by simpa [Metric.mem_closedBall, dist_eq_norm] using h⟩

omit [Nontrivial E] in
/-- One chosen nonzero global LMO identifies the unknown center at equal
radii, directly from the rolling-ball hypotheses on the body. -/
theorem equal_radii_recovery {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r : ℝ}
    (hr : 0 < r) (innerBall : InnerBall C r) (outer : OuterBall C r) (O : LMO C) (e : E)
        (he : e ≠ 0) :
    erosion C r = {unwrap O r e} ∧ C = Metric.closedBall (unwrap O r e) r := by
  have rep := parallel_of_normals hc cv ⟨_, O.mem e⟩ hr (normals_of_inner hr.le innerBall) he
  exact equal_radii_center rep hr outer O e he

theorem analytic_parameters {f : E → ℝ} {L : ℝ≥0} {μ : ℝ} (hμ : 0 < μ)
    (df : Differentiable ℝ f) (sc : StrongConvexOn Set.univ μ f) (smooth : LipschitzWith L (∇ f))
        (C : Set E) :
    Models C f (∇ f) L ∧ StrongLower C f (∇ f) μ ∧ μ ≤ L := by
  have convex := strongConvexOn_zero.mp (sc.mono hμ.le)
  let mdl := models_of_convex_lipschitz df convex smooth
  obtain ⟨e, ne⟩ := exists_ne (0 : E)
  have u := (mdl Set.univ).upper 0 (Set.mem_univ _) e (Set.mem_univ _)
  have l := strong_lower_of_strongConvexOn df sc Set.univ 0 (Set.mem_univ _) e (Set.mem_univ _)
  simp only [sub_zero] at u l
  have pos : 0 < ‖e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ne)
  refine ⟨mdl C, strong_lower_of_strongConvexOn df sc C, ?_⟩
  apply le_of_mul_le_mul_right (a := ‖e‖ ^ 2) _ pos
  linarith only [u, l]

omit [ProperSpace E] in
theorem linear_of_parallel_rep {C K : Set E} {r R L μ : ℝ} (rep : C = Rounded K r)
    (hk : Convex ℝ K) (hc : IsCompact C) (cv : Convex ℝ C) (hr : 0 < r) (hR : r ≤ R)
    (outer : OuterBall C R) (O : LMO C) {f : E → ℝ} {g : E → E}
    (mdl : Models C f g L) (strong : StrongLower C f g μ) (hμ : 0 < μ) (hLμ : μ ≤ L)
    (ball : Bool) (cert : ball = true → R = r) {x₀ : E} (hx : x₀ ∈ C) (n : ℕ) :
    let ans := projectedGradientRun O g L r ball x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
    ∀ w ∈ C, f ans.1 - f w ≤ (1 - share r R * (μ / L)) ^ n * (L / 2 * (Metric.diam C) ^ 2) := by
  subst C
  have B := share_bounds hr hR
  have reg : Regime K r (share r R) ball := by
    by_cases eq : R = r
    · subst R
      obtain ⟨e, he⟩ := exists_ne (0 : E)
      obtain ⟨Krep, _⟩ := equal_radii_center rfl hr outer O e he
      exact Or.inl (fun a ha v hv => by
        rw [Krep] at ha hv
        exact (show a = unwrap O r e from ha).trans (show v = unwrap O r e from hv).symm)
    · have pos : 0 < R - r := sub_pos.mpr (lt_of_le_of_ne hR (Ne.symm eq))
      have flag : ball = false := by cases ball <;> simp_all
      have s := share_spec hr pos
      exact Or.inr ⟨flag, R - r, pos, core_outer hr.le hR outer, by simpa [share, eq] using s.2.1,
        by simpa [share, eq] using s.2.2⟩
  exact parallel_linear_upper hk cv O mdl strong hr hμ hLμ B.1.le B.2 reg hx
    (fun y hy => diameter_width hc y hy _ hx) n

/-- Ordinary global body LMO, a gradient at a feasible point and closed-form arithmetic.
All constants in the rate, including the uniform first-step gap, are derived. -/
theorem joint_body_linear_upper {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r R μ : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (innerBall : InnerBall C r) (outer : OuterBall C R)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hμ : 0 < μ) (df : Differentiable ℝ f)
    (sc : StrongConvexOn Set.univ μ f) (smooth : LipschitzWith L (∇ f))
    (ball : Bool) (cert : ball = true → R = r) {x₀ : E} (hx : x₀ ∈ C) (n : ℕ) :
    let ans := projectedGradientRun O (∇ f) L r ball x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n * (if ball then 0 else 1) ∧ ans.2.2 ≤ 1 + n ∧
    ∀ w ∈ C, f ans.1 - f w ≤
      (1 - share r R * (μ / L)) ^ n * ((L : ℝ) / 2 * (Metric.diam C) ^ 2) := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  obtain ⟨mdl, strong, lge⟩ := analytic_parameters hμ df sc smooth C
  have eq := parallel_of_normals hc cv ⟨_, hx⟩ hr (normals_of_inner hr.le innerBall) he
  exact linear_of_parallel_rep eq (erosion_compact_convex hc cv hr.le).2 hc cv hr hR outer O mdl
    strong hμ lge ball cert hx n

theorem joint_ball_linear_upper {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r μ : ℝ}
    (hr : 0 < r) (innerBall : InnerBall C r) (outer : OuterBall C r)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hμ : 0 < μ) (df : Differentiable ℝ f)
    (sc : StrongConvexOn Set.univ μ f) (smooth : LipschitzWith L (∇ f))
    {x₀ : E} (hx : x₀ ∈ C) (n : ℕ) :
    let ans := projectedGradientRun O (∇ f) L r true x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 ∧ ans.2.2 ≤ 1 + n ∧
    ∀ w ∈ C, f ans.1 - f w ≤ (1 - μ / L) ^ n * ((L : ℝ) / 2 * (Metric.diam C) ^ 2) := by
  simpa [share] using joint_body_linear_upper hc cv hr (le_refl r) innerBall outer O hμ df sc
    smooth true (fun _ => rfl) hx n

/-- Equivalent geometry using a bound on supporting normals and the chord-ball
strong-convexity condition. The code needs neither R nor μ as an input. -/
theorem chord_body_linear_upper {C : Set E} (hc : IsCompact C) (cv : Convex ℝ C) {r R μ : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (normal : NormalBound C r) (chord : ChordBall C R)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hμ : 0 < μ) (df : Differentiable ℝ f)
    (sc : StrongConvexOn Set.univ μ f) (smooth : LipschitzWith L (∇ f))
    {x₀ : E} (hx : x₀ ∈ C) (n : ℕ) :
    let ans := projectedGradientRun O (∇ f) L r false x₀ n
    ans.1 ∈ C ∧ ans.2.1 ≤ 1 + n ∧ ans.2.2 ≤ 1 + n ∧
    ∀ w ∈ C, f ans.1 - f w ≤
      (1 - share r R * (μ / L)) ^ n * ((L : ℝ) / 2 * (Metric.diam C) ^ 2) := by
  simpa using joint_body_linear_upper hc cv hr hR (inner_of_normals hc cv hr normal)
    (outer_of_chord (hr.trans_le hR) chord) O hμ df sc smooth false (by simp) hx n

end Lemmata.FrankWolfePS.Joint
