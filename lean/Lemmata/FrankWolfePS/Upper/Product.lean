module

public import Lemmata.FrankWolfePS.Upper.LineSearch
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Pair (E : Type*) := WithLp 2 (E × E)
def pair (a b : E) : Pair E := WithLp.toLp 2 (a, b)
def total (v : Pair E) : E := v.fst + v.snd
def domain (K : Set E) (r : ℝ) : Set (Pair E) := {p | p.fst ∈ K ∧ ‖p.snd‖ ≤ r}

omit [InnerProductSpace ℝ E] in
theorem total_mem {K : Set E} {r : ℝ} {v : Pair E} (hv : v ∈ domain K r) :
    total v ∈ Rounded K r := ⟨v.fst, hv.1, by simpa [total] using hv.2⟩

theorem domain_convex {K : Set E} (hK : Convex ℝ K) (r : ℝ) : Convex ℝ (domain K r) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hK hx.1 hy.1 ha hb hab, ?_⟩
  have bx : x.snd ∈ Metric.closedBall 0 r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have by' : y.snd ∈ Metric.closedBall 0 r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy.2
  have H := (convex_closedBall (0 : E) r) bx by' ha hb hab
  simpa [Metric.mem_closedBall, dist_eq_norm] using H

omit [InnerProductSpace ℝ E] in
theorem product_width {K : Set E} {δ r : ℝ} (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ)
    (v : Pair E) (hv : v ∈ domain K r) (w : Pair E) (hw : w ∈ domain K r) :
    ‖v - w‖ ^ 2 ≤ δ ^ 2 + 4 * r ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd]
  have h := pow_le_pow_left₀ (norm_nonneg _) (width v.fst hv.1 w.fst hw.1) 2
  have h' : ‖v.snd - w.snd‖ ≤ 2 * r := by linarith [norm_sub_le v.snd w.snd, hv.2, hw.2]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h' 2]

omit [InnerProductSpace ℝ E] in
theorem total_diff (v w : Pair E) : total v - total w = (v.fst - w.fst) + (v.snd - w.snd) := by
  unfold total; abel

theorem product_models {K : Set E} {r L : ℝ} (hL : 0 ≤ L) {f : E → ℝ} {g : E → E}
    (mdl : Models (Rounded K r) f g L) :
    Models (domain K r) (fun v => f (total v)) (fun v =>
        pair (g (total v)) (g (total v))) (2 * L) := by
  have hin (v w : Pair E) :
      ⟪pair (g (total v)) (g (total v)), w - v⟫ = ⟪g (total v), total w - total v⟫ := by
    rw [total_diff, inner_add_right]; rfl
  constructor
  · intro v hv w hw; rw [hin]; exact mdl.lower _ (total_mem hv) _ (total_mem hw)
  · intro v hv w hw
    rw [hin]
    have H := mdl.upper _ (total_mem hv) _ (total_mem hw)
    have hn := norm_add_le (w.fst - v.fst) (w.snd - v.snd)
    have hq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have bound : ‖total w - total v‖ ^ 2 ≤ 2 * ‖w - v‖ ^ 2 := by
      rw [total_diff, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd]
      nlinarith [_root_.sq_nonneg (‖w.fst - v.fst‖ - ‖w.snd - v.snd‖)]
    linarith only [H, mul_le_mul_of_nonneg_left bound hL]

noncomputable def ballProx (q c : E) (τ r : ℝ) : E := clip r (c - τ⁻¹ • q)

theorem ballProx_gap (q c : E) {τ r : ℝ} (hτ : 0 < τ) (hr : 0 ≤ r) {b : E} (hb : ‖b‖ ≤ r) :
    let a := ballProx q c τ r
    ⟪q + τ • (a - c), a - b⟫ ≤ 0 := by
  let a := ballProx q c τ r
  have h := clip_vi hr (c - τ⁻¹ • q) b hb
  change ⟪(c - τ⁻¹ • q) - a, b - a⟫ ≤ 0 at h
  have e : τ • ((c - τ⁻¹ • q) - a) = -(q + τ • (a - c)) := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]; abel
  have h1 := mul_nonpos_of_nonneg_of_nonpos hτ.le h
  rw [← real_inner_smul_left, e, inner_neg_left, show b - a =
      -(a - b) by abel, inner_neg_right, neg_neg] at h1
  exact h1

noncomputable def productInner (oracle : E → E) (q : E) (c : Pair E) (τ δ η r : ℝ) : Pair E × ℕ :=
  let a := innerLineRun oracle q c.fst τ δ η
  (pair a.1 (ballProx q c.snd τ r), a.2)

theorem productInner_spec {K : Set E} (hK : Convex ℝ K) (O : LMO K) {δ r τ η : ℝ}
    (hr : 0 ≤ r) (hτ : 0 < τ) (hη : 0 < η) (width : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ δ)
    (q : E) (c : Pair E) (hc : c ∈ domain K r) :
    let v := productInner O.query q c τ δ η r
    v.1 ∈ domain K r ∧
    (∀ w ∈ domain K r, ⟪pair q q + τ • (v.1 - c), v.1 - w⟫ ≤ η) ∧
    (v.2 : ℝ) ≤ 1 + 6 * τ * δ ^ 2 / η := by
  let a := innerLineRun O.query q c.fst τ δ η
  let b := ballProx q c.snd τ r
  obtain ⟨ha, hg, hcnt⟩ := innerLineRun_spec hK O hτ.le hη width q c.fst hc.1
  refine ⟨⟨ha, norm_clip hr _⟩, ?_, hcnt⟩
  intro w hw
  change ⟪proxGrad q c.fst τ a.1, a.1 - w.fst⟫ + ⟪q + τ • (b - c.snd), b - w.snd⟫ ≤ η
  linarith only [hg w.fst hw.1, ballProx_gap q c.snd hτ hr hw.2]

end Lemmata.FrankWolfePS.Upper
