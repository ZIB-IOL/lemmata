module

public import Lemmata.FrankWolfePS.Upper.Converse
public import Lemmata.FrankWolfePS.Upper.Quadratic
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- `C` is `β`-smooth: unit outer normals `n` at `z ∈ C` and `m` at `y ∈ C` satisfy
`‖n - m‖ ≤ β ‖z - y‖`. -/
def LipschitzNormals (C : Set E) (β : ℝ) : Prop :=
  ∀ z ∈ C, ∀ y ∈ C, ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → Supports C z n → Supports C y m →
    ‖n - m‖ ≤ β * ‖z - y‖

omit [ProperSpace E] in
theorem radius_regular {C : Set E} {β : ℝ} (hβ : 0 < β) (h : LipschitzNormals C β) :
    NormalBound C (1 / β) := by
  intro x hx y hy n m hn hm hs ht
  rw [norm_sub_rev m n, norm_sub_rev y x, one_div_mul_eq_div]
  exact (div_le_iff₀ hβ).mpr (by simpa [mul_comm] using h x hx y hy n m hn hm hs ht)

omit [InnerProductSpace ℝ E] [ProperSpace E] in
theorem diameter_width {C : Set E} (hc : IsCompact C) (x : E) (hx : x ∈ C) (y : E) (hy : y ∈ C) :
    ‖x - y‖ ≤ Metric.diam C := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hc.isBounded hx hy

omit [ProperSpace E] in
theorem quadratic_of_rep {C K : Set E} (eq : C = Rounded K (r : ℝ)) (hK : Convex ℝ K)
    (hc : IsCompact C) (hr : 0 < r) (hD : 2 * r ≤ Metric.diam C) {L : ℝ} (hL : 0 < L)
    (O : LMO C) (u e : E) (he : e ≠ 0) (n : ℕ) :
    let ans := quadraticRun O (isoGrad L u) L r e (n + 1)
    ans.1 ∈ C ∧ ans.2.1 ≤ n + 2 ∧ ans.2.2 = 1 ∧ ∀ w ∈ C, iso L u ans.1 - iso L u w ≤
      2 * L * (Metric.diam C - 2 * r) ^ 2 / ((n : ℝ) + 3) := by
  subst C
  exact quadratic_parallel_upper hK hr hD hL (diameter_width hc) O u e he n

/-- T=n+2 allowed body LMO calls, one gradient, and gap at most
2L(diam C−2/β)^2/(T+1), using only C's numerical oracle. -/
theorem quadratic_smooth_body_upper {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (regular : LipschitzNormals C β)
    (hD : 2 * (1 / β) ≤ Metric.diam C) (O : LMO C) (u e : E) (he : e ≠ 0) (n : ℕ) :
    let ans := quadraticRun O (isoGrad L u) L (1 / β) e (n + 1)
    ans.1 ∈ C ∧ ans.2.1 ≤ n + 2 ∧ ans.2.2 = 1 ∧ ∀ w ∈ C, iso L u ans.1 - iso L u w ≤
      2 * L * (Metric.diam C - 2 * (1 / β)) ^ 2 / ((n : ℝ) + 3) := by
  have hr : 0 < 1 / β := by positivity
  exact quadratic_of_rep (parallel_of_normals hc hv ⟨_, O.mem e⟩ hr (radius_regular hβ regular) he)
    (erosion_compact_convex hc hv hr.le).2 hc hr hD hL O u e he n

omit [ProperSpace E] in
private theorem ball_of_rep {C K : Set E} {r L : ℝ} (eq : C = Rounded K r)
    (hc : IsCompact C) (hr : 0 < r) (hL : 0 < L) (hd : Metric.diam C = 2 * r) (O : LMO C)
    (u e : E) (he : e ≠ 0) :
    let ans := quadraticRun O (isoGrad L u) L r e 0
    ans.1 ∈ C ∧ ans.2 = (1, 1) ∧ ∀ w ∈ C, iso L u ans.1 ≤ iso L u w := by
  subst C
  exact quadratic_ball_exact hr hL (hd ▸ diameter_width hc) O u e he

theorem quadratic_smooth_ball_exact {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (regular : LipschitzNormals C β)
    (hd : Metric.diam C = 2 * (1 / β)) (O : LMO C) (u e : E) (he : e ≠ 0) :
    let ans := quadraticRun O (isoGrad L u) L (1 / β) e 0
    ans.1 ∈ C ∧ ans.2 = (1, 1) ∧ ∀ w ∈ C, iso L u ans.1 ≤ iso L u w := by
  have hr : 0 < 1 / β := by positivity
  exact ball_of_rep (parallel_of_normals hc hv ⟨_, O.mem e⟩ hr (radius_regular hβ regular) he)
    hc hr hL hd O u e he

/-- The center and curvature are public. Inline the explicit gradient as local
arithmetic; the only external oracle argument is the body LMO. -/
noncomputable def disclosedRun {C : Set E} (O : LMO C) (u : E) (L r : ℝ)
    (e : E) (steps : ℕ) : E × ℕ × ℕ :=
  let v := quadraticRun O (isoGrad L u) L r e steps
  (v.1, v.2.1, 0)

theorem disclosed_quadratic_upper {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (regular : LipschitzNormals C β)
    (hD : 2 * (1 / β) ≤ Metric.diam C) (O : LMO C) (u e : E) (he : e ≠ 0) (n : ℕ) :
    let ans := disclosedRun O u L (1 / β) e (n + 1)
    ans.1 ∈ C ∧ ans.2.1 ≤ n + 2 ∧ ans.2.2 = 0 ∧ ∀ w ∈ C, iso L u ans.1 - iso L u w ≤
      2 * L * (Metric.diam C - 2 * (1 / β)) ^ 2 / ((n : ℝ) + 3) := by
  obtain ⟨hm, hc', _, hg⟩ := quadratic_smooth_body_upper hc hv hβ hL regular hD O u e he n
  exact ⟨hm, hc', rfl, hg⟩

theorem disclosed_ball_exact {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (regular : LipschitzNormals C β)
    (hd : Metric.diam C = 2 * (1 / β)) (O : LMO C) (u e : E) (he : e ≠ 0) :
    let ans := disclosedRun O u L (1 / β) e 0
    ans.1 ∈ C ∧ ans.2 = (1, 0) ∧ ∀ w ∈ C, iso L u ans.1 ≤ iso L u w := by
  obtain ⟨hm, _, hg⟩ := quadratic_smooth_ball_exact hc hv hβ hL regular hd O u e he
  exact ⟨hm, rfl, hg⟩

/-- A coincident first-order lower and upper quadratic model is enough; the
full objective is not an algorithm input and an arbitrary additive constant cancels. -/
theorem equal_curvature_upper {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β L : ℝ} (hβ : 0 < β) (hL : 0 < L) (reg : LipschitzNormals C β)
    (hD : 2 * (1 / β) ≤ Metric.diam C) (O : LMO C) (f : E → ℝ) (g : E → E)
    (eqModel : ∀ x ∈ C, ∀ y ∈ C, f y = f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (e : E) (he : e ≠ 0) (n : ℕ) :
    let ans := quadraticRun O g L (1 / β) e (n + 1)
    ans.1 ∈ C ∧ ans.2.1 ≤ n + 2 ∧ ans.2.2 = 1 ∧ ∀ w ∈ C, f ans.1 - f w ≤
      2 * L * (Metric.diam C - 2 * (1 / β)) ^ 2 / ((n : ℝ) + 3) := by
  let z := O.query e
  let u := z - L⁻¹ • g z
  have gs : isoGrad L u z = g z := by simp [isoGrad, u, smul_smul, hL.ne']
  have same (y : E) (hy : y ∈ C) : f y - iso L u y = f z - iso L u z := by
    rw [eqModel z (O.mem e) y hy, iso_taylor L u z y, gs]; ring
  let ans := quadraticRun O g L (1 / β) e (n + 1)
  have eqR : quadraticRun O (isoGrad L u) L (1 / β) e (n + 1) = ans := by
    change quadraticRun O (isoGrad L u) L (1 / β) e (n + 1) = quadraticRun O g L (1 / β) e (n + 1)
    simp only [quadraticRun, show isoGrad L u (O.query e) = g (O.query e) from gs]
  have h := quadratic_smooth_body_upper hc hv hβ hL reg hD O u e he n
  dsimp only at h
  rw [eqR] at h
  refine ⟨h.1, h.2.1, h.2.2.1, fun w hw => ?_⟩
  change f ans.1 - f w ≤ _
  linarith only [h.2.2.2 w hw, same ans.1 h.1, same w hw]

/-- Apply the matching upper bound to the exact selector and the tilted
physical objective from the lower bound. -/
theorem hard_family_quadratic_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    {a r L : ℝ} (ha : 0 < a) (hr : 0 < r) (hL : 0 < L) {I : Finset ι} (hI : 1 < I.card)
    {anchor : ι} (hi : anchor ∈ I) (e : Ambient ι) (he : e ≠ 0) (n : ℕ) :
    let C := physicalBody a r I
    let O : LMO C := ⟨fun q => a • oracle (r / a) anchor I q,
      fun q => (physical_oracle_correct ha hr anchor hi q).1,
      fun q _ hw => (physical_oracle_correct ha hr anchor hi q).2 _ hw⟩
    let c := embed (fun _ : ι => 0, 32 * L * r)
    let ans := quadraticRun O (Lemmata.FrankWolfePS.grad L c) L r e (n + 1)
    ans.1 ∈ C ∧ ans.2.1 ≤ n + 2 ∧ ans.2.2 = 1 ∧
      ∀ w ∈ C, Lemmata.FrankWolfePS.quadratic L c ans.1 - Lemmata.FrankWolfePS.quadratic L c w ≤
          4 * L * a ^ 2 / ((n : ℝ) + 3) := by
  let C := physicalBody a r I
  let O : LMO C := ⟨fun q => a • oracle (r / a) anchor I q,
    fun q => (physical_oracle_correct ha hr anchor hi q).1,
    fun q _ hw => (physical_oracle_correct ha hr anchor hi q).2 _ hw⟩
  let c := embed (fun _ : ι => 0, 32 * L * r)
  have cp := physical_body_compact_convex (a := a) (r := r) I
  have h := physical_parameters ha hr I hI
  have hinv : 1 / (1 / r) = r := by field_simp
  have hD : 2 * (1 / (1 / r)) ≤ Metric.diam C := by
    rw [hinv, h.1]; linarith [mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) ha]
  have main := equal_curvature_upper cp.1 cp.2 (by positivity : 0 < 1 / r) hL h.2 hD O
    (Lemmata.FrankWolfePS.quadratic L c) (Lemmata.FrankWolfePS.grad L c)
        (fun x _ y _ => quadratic_taylor L c x y) e he n
  dsimp only at main ⊢
  rw [hinv] at main
  refine ⟨main.1, main.2.1, main.2.2.1, fun w hw => ?_⟩
  have bound := main.2.2.2 w hw
  rw [h.1, add_sub_cancel_left, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at bound
  convert bound using 1; ring

end Lemmata.FrankWolfePS.Upper
