module

public import Lemmata.FrankWolfePS.Upper.Joint
@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped Gradient NNReal

/-- The chosen number of real gradient calls and an explicit sequential
padding bound. A is the squared product diameter and B the squared core width. -/
theorem tolerance_arithmetic {L A B ε : ℝ} (hL : 0 < L) (hA : 0 < A) (hB : 0 ≤ B) (hBA : B ≤ A)
    (hε : 0 < ε) :
    let x := Real.sqrt (15 * L * A / ε)
    let n := ⌈x⌉₊
    0 < n ∧ 15 * (2 * L) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ ε ∧
    1 + (n : ℝ) + 9 * B * (n : ℝ) * ((n : ℝ) + 1) / A + n ≤ 48 + 2 * x + 270 * L * B / ε := by
  let x := Real.sqrt (15 * L * A / ε)
  let n := ⌈x⌉₊
  have x0 : 0 < x := Real.sqrt_pos_of_pos (by positivity)
  have x2 : x ^ 2 = 15 * L * A / ε := Real.sq_sqrt (by positivity)
  have nx : x ≤ (n : ℝ) := Nat.le_ceil _
  have xn : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one x0.le
  have np : 0 < (n : ℝ) := x0.trans_le nx
  have npos : 0 < n := by exact_mod_cast np
  refine ⟨npos, ?_, ?_⟩
  · apply (div_le_iff₀ (show 0 < 2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) by positivity)).mpr
    have hsq := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ x0.le nx 2) hε.le
    have eq := (eq_div_iff hε.ne').mp x2
    nlinarith [mul_pos hε np]
  · have hquad : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * x ^ 2 + 5 := by
      have h := mul_le_mul xn.le (add_le_add xn.le (le_refl (1 : ℝ)))
        (by positivity : 0 ≤ (n : ℝ) + 1) (by positivity : 0 ≤ x + 1)
      nlinarith [_root_.sq_nonneg (x - 3 / 2)]
    have hb : B / A ≤ 1 := (div_le_one hA).mpr hBA
    have ho := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 9 * (B / A) by positivity)
    have id : 9 * (B / A) * (2 * x ^ 2 + 5) = 270 * L * B / ε + 45 * (B / A) := by
      rw [x2]; field_simp; ring
    rw [id] at ho
    change 1 + (n : ℝ) + 9 * B * (n : ℝ) * ((n : ℝ) + 1) / A + n ≤ 48 + 2 * x + 270 * L * B / ε
    simp only [div_eq_mul_inv] at hb ho ⊢
    linarith only [hb, ho, xn]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- ε-complexity with explicit constants for sending each real query in a
separate paired slot. The objective and body are available only via the two oracles. -/
theorem smooth_body_paired_tolerance {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β : ℝ} (hβ : 0 < β) (regular : LipschitzNormals C β) (hD : 2 * (1 / β) ≤ Metric.diam C)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hL : 0 < (L : ℝ)) (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (hLip : LipschitzWith L (∇ f)) (e : E) (he : e ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    let r := 1 / β
    let D := Metric.diam C
    let δ := D - 2 * r
    let n := ⌈Real.sqrt (15 * (L : ℝ) * (δ ^ 2 + 4 * r ^ 2) / ε)⌉₊
    let ans := slidingRun O (∇ f) L r D e n
    ans.1 ∈ C ∧ (∀ w ∈ C, f ans.1 - f w ≤ ε) ∧ ans.2.2 = n ∧
    ((ans.2.1 + ans.2.2 : ℕ) : ℝ) ≤ 48 + 2 * Real.sqrt (15 * (L : ℝ) * D ^ 2 / ε) + 270 *
        (L : ℝ) * δ ^ 2 / ε := by
  let r := 1 / β
  let D := Metric.diam C
  let δ := D - 2 * r
  let A := δ ^ 2 + 4 * r ^ 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hd : 0 ≤ δ := sub_nonneg.mpr hD
  have hA : 0 < A := by dsimp [A]; positivity
  have ba : δ ^ 2 ≤ A := by dsimp [A]; linarith [_root_.sq_nonneg r]
  have da : A ≤ D ^ 2 := by
    dsimp [A, δ]; nlinarith [mul_nonneg hd hr.le, show D = δ + 2 * r by dsimp [δ]; ring]
  let n := ⌈Real.sqrt (15 * (L : ℝ) * A / ε)⌉₊
  obtain ⟨np, rate, count⟩ := tolerance_arithmetic hL hA (_root_.sq_nonneg δ) ba hε
  obtain ⟨hm, ng, cnt, gap⟩ :=
      smooth_body_sliding_upper hc hv hβ regular hD O hL hf hconv hLip e he np
  refine ⟨hm, fun w hw => (gap w hw).trans rate, ng, ?_⟩
  have root := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left da (show 0 ≤
      15 * (L : ℝ) by positivity)) hε.le)
  rw [Nat.cast_add, ng]
  change _ ≤ 48 + 2 * Real.sqrt (15 * (L : ℝ) * D ^ 2 / ε) + 270 * (L : ℝ) * δ ^ 2 / ε
  change _ ≤ 1 + (n : ℝ) + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A at cnt
  change 1 + (n : ℝ) + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A + n ≤ 48 +
      2 * Real.sqrt (15 * (L : ℝ) * A / ε) + 270 * (L : ℝ) * δ ^ 2 / ε at count
  linarith only [count, cnt, root]

/-- Inversion of the verified tolerance bound into an explicit number of paired calls. -/
theorem call_count_inverse {D δ L T : ℝ} (hL : 0 < L) (hD : 0 < D) (hT : 144 ≤ T) :
    let ε := 540 * L * D ^ 2 / T ^ 2 + 810 * L * δ ^ 2 / T
    0 < ε ∧ 48 + 2 * Real.sqrt (15 * L * D ^ 2 / ε) + 270 * L * δ ^ 2 / ε ≤ T := by
  have ht : 0 < T := by linarith
  let ε := 540 * L * D ^ 2 / T ^ 2 + 810 * L * δ ^ 2 / T
  have he : 0 < ε := by dsimp [ε]; positivity
  have he1 : 540 * L * D ^ 2 / T ^ 2 ≤ ε := by
    dsimp [ε]; linarith [show 0 ≤ 810 * L * δ ^ 2 / T by positivity]
  have he2 : 810 * L * δ ^ 2 / T ≤ ε := by
    dsimp [ε]; linarith [show 0 ≤ 540 * L * D ^ 2 / T ^ 2 by positivity]
  have A := (div_le_iff₀ (sq_pos_of_pos ht)).mp he1
  have B := (div_le_iff₀ ht).mp he2
  have sq : 15 * L * D ^ 2 / ε ≤ (T / 6) ^ 2 := (div_le_iff₀ he).mpr (by nlinarith only [A])
  have root : Real.sqrt (15 * L * D ^ 2 / ε) ≤ T / 6 := (Real.sqrt_le_iff).mpr ⟨by positivity, sq⟩
  have last : 270 * L * δ ^ 2 / ε ≤ T / 3 := (div_le_iff₀ he).mpr (by linarith only [B])
  exact ⟨he, by linarith only [hT, root, last]⟩

theorem smooth_body_paired_calls {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β : ℝ} (hβ : 0 < β) (regular : LipschitzNormals C β) (hD : 2 * (1 / β) ≤ Metric.diam C)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hL : 0 < (L : ℝ)) (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (hLip : LipschitzWith L (∇ f)) (e : E) (he : e ≠ 0)
    {T : ℕ} (hT : 144 ≤ T) :
    let r := 1 / β
    let D := Metric.diam C
    let δ := D - 2 * r
    let ε := 540 * (L : ℝ) * D ^ 2 / (T : ℝ) ^ 2 + 810 * (L : ℝ) * δ ^ 2 / (T : ℝ)
    let n := ⌈Real.sqrt (15 * (L : ℝ) * (δ ^ 2 + 4 * r ^ 2) / ε)⌉₊
    let ans := slidingRun O (∇ f) L r D e n
    ans.1 ∈ C ∧ ans.2.1 + ans.2.2 ≤ T ∧ ∀ w ∈ C, f ans.1 - f w ≤ ε := by
  let r := 1 / β
  let D := Metric.diam C
  let δ := D - 2 * r
  have hr : 0 < r := by dsimp [r]; positivity
  have dpos : 0 < D := (show 0 < 2 * r by positivity).trans_le hD
  have hT' : (144 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨hε, count⟩ := call_count_inverse (δ := δ) hL dpos hT'
  obtain ⟨hm, hg, _, hc'⟩ :=
      smooth_body_paired_tolerance hc hv hβ regular hD O hL hf hconv hLip e he hε
  refine ⟨hm, ?_, hg⟩
  exact_mod_cast hc'.trans count

end Lemmata.FrankWolfePS.Upper
