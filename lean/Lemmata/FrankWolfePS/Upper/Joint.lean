module

public import Lemmata.FrankWolfePS.Upper.Sliding
public import Lemmata.FrankWolfeLDS.Proof.Smoothness

@[expose] public section

namespace Lemmata.FrankWolfePS.Upper
open scoped RealInnerProductSpace Gradient NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Two analytic facts imported directly from the pinned Lemmata archive. -/
theorem models_of_convex_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : Differentiable ℝ f)
    (hv : ConvexOn ℝ Set.univ f) (hLip : LipschitzWith L (∇ f)) (C : Set E) :
    Models C f (∇ f) (L : ℝ) :=
  ⟨fun x _ y _ => Lemmata.FrankWolfeLDS.isFirstOrderConvex_of_convexOn hf hv x y,
   fun x _ y _ => Lemmata.FrankWolfeLDS.isLipschitzSmoothUpperBound_of_lipschitzWith hf hLip x y⟩

omit [ProperSpace E] in
private theorem slide_of_rep {C K : Set E} {r L : ℝ} (eq : C = Rounded K r)
    (hK : Convex ℝ K) (hc : IsCompact C) (hr : 0 < r) (hL : 0 < L) (hD : 2 * r ≤ Metric.diam C)
    (O : LMO C) {f : E → ℝ} {g : E → E} (mdl : Models C f g L) (e : E) (he : e ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    let δ := Metric.diam C - 2 * r
    let A := δ ^ 2 + 4 * r ^ 2
    let ans := slidingRun O g L r (Metric.diam C) e n
    ans.1 ∈ C ∧ ans.2.2 = n ∧ (ans.2.1 : ℝ) ≤ 1 + n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A ∧
      ∀ w ∈ C, f ans.1 - f w ≤ 15 * (2 * L) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  subst C
  exact sliding_parallel_upper hK hr hL hD (diameter_width hc) O mdl e he hn

/-- Smooth convex objectives with ordinary Lipschitz gradient; the hidden core
is absent from the input and every genuine gradient query is feasible. -/
theorem smooth_body_sliding_upper {C : Set E} (hc : IsCompact C) (hv : Convex ℝ C)
    {β : ℝ} (hβ : 0 < β) (regular : LipschitzNormals C β) (hD : 2 * (1 / β) ≤ Metric.diam C)
    (O : LMO C) {f : E → ℝ} {L : ℝ≥0} (hL : 0 < (L : ℝ)) (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ Set.univ f) (hLip : LipschitzWith L (∇ f))
    (e : E) (he : e ≠ 0) {n : ℕ} (hn : 0 < n) :
    let r := 1 / β
    let δ := Metric.diam C - 2 * r
    let A := δ ^ 2 + 4 * r ^ 2
    let ans := slidingRun O (∇ f) L r (Metric.diam C) e n
    ans.1 ∈ C ∧ ans.2.2 = n ∧ (ans.2.1 : ℝ) ≤ 1 + n + 9 * δ ^ 2 * (n : ℝ) * ((n : ℝ) + 1) / A ∧
      ∀ w ∈ C, f ans.1 - f w ≤ 15 * (2 * (L : ℝ)) * A / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hr : 0 < 1 / β := by positivity
  exact slide_of_rep (parallel_of_normals hc hv ⟨_, O.mem e⟩ hr (radius_regular hβ regular) he)
    (erosion_compact_convex hc hv hr.le).2 hc hr hL hD O
        (models_of_convex_lipschitz hf hconv hLip C) e he hn

end Lemmata.FrankWolfePS.Upper
