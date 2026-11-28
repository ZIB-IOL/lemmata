module

public import Lemmata.FWProduct.Upper
public import Lemmata.FrankWolfe.Polytope.Faces

@[expose] public section

/-!
# The two widths agree

Lemma 4.3 and Corollary 4.4: the affine pyramidal width equals the pyramidal width (the facial
distance). The paper argues with a facet whose affine hull separates a point from a face; the
formal proof avoids facets. If `a ∈ aff F` lies outside `conv F`, the segment from `a` to the
barycenter `b` of `F` enters `conv F` at a point `p'` whose minimal face `G` is a proper face of
`F`, by the relative-interior property of minimal faces (`push_away`). Splitting `b` into the
barycenters of `G` and of `F \ G`, the segment from `a` to the barycenter `r` of `F \ G` meets the
affine hull of `G` at `z = a + τ (r - a)` with `τ > 0`, and `q + τ (r - q)` lies in `conv (V \ G)`
at distance `(1 - τ) ‖a - q‖` from `z`. Induction on the size of the face gives Corollary 4.4; the
strict decrease gives Lemma 4.3.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

section Faces

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A functional that is constant on `F` is constant on the affine hull of `F`. -/
theorem apply_eq_of_mem_affineSpan {F : Set E} (ψ : StrongDual ℝ E) {M : ℝ}
    (hF : ∀ w ∈ F, ψ w = M) {y : E} (hy : y ∈ affineSpan ℝ F) : ψ y = M := by
  refine affineSpan_induction (p := fun y => ψ y = M) hy hF ?_
  intro c u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul, hu, hv, hw,
    sub_self, mul_zero, zero_add]

open Classical in
/-- An exposed face of an exposed face is an exposed face: perturb the first functional by a small
multiple of the second. -/
theorem exists_exposedFace_eq (V : Finset E) (ψ Ψ : StrongDual ℝ E) :
    ∃ Φ : StrongDual ℝ E, exposedFace V Φ = exposedFace (exposedFace V ψ) Ψ := by
  classical
  set F := exposedFace V ψ with hFdef
  rcases V.eq_empty_or_nonempty with hV | hV
  · refine ⟨Ψ, ?_⟩
    have hF0 : F = ∅ := Finset.subset_empty.mp (hV ▸ exposedFace_subset V ψ)
    rw [hF0, hV]
  obtain ⟨f₀, hf₀⟩ := Proof.exposedFace_nonempty hV ψ
  have hfF : ∀ w ∈ F, w ∈ V ∧ ∀ u ∈ V, ψ u ≤ ψ w := fun w hw => by
    rw [hFdef] at hw
    unfold exposedFace at hw
    exact Finset.mem_filter.mp hw
  have hconst : ∀ w ∈ F, ψ w = ψ f₀ := fun w hw =>
    le_antisymm ((hfF f₀ hf₀).2 w (hfF w hw).1) ((hfF w hw).2 f₀ (hfF f₀ hf₀).1)
  rcases (V \ F).eq_empty_or_nonempty with hVF | hVF
  · have hFV : F = V :=
      Finset.Subset.antisymm (exposedFace_subset V ψ) (Finset.sdiff_eq_empty_iff_subset.mp hVF)
    exact ⟨Ψ, by rw [hFV]⟩
  have hgap : ∀ w ∈ V \ F, ψ w < ψ f₀ := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    by_contra hlt
    have hlt := not_lt.mp hlt
    apply hw.2
    rw [hFdef]
    unfold exposedFace
    exact Finset.mem_filter.mpr ⟨hw.1, fun u hu => ((hfF f₀ hf₀).2 u hu).trans hlt⟩
  set δ₀ := (V \ F).inf' hVF (fun w => ψ f₀ - ψ w) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_inf'_iff]; intro w hw; linarith [hgap w hw]
  have hδ₀le : ∀ w ∈ V \ F, δ₀ ≤ ψ f₀ - ψ w := fun w hw => Finset.inf'_le _ hw
  set K := ∑ w ∈ V, |Ψ w| with hK
  have hKle : ∀ w ∈ V, |Ψ w| ≤ K := fun w hw =>
    Finset.single_le_sum (f := fun w => |Ψ w|) (fun w _ => abs_nonneg (Ψ w)) hw
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun w _ => abs_nonneg _)
  set ε := δ₀ / (2 * K + 1) with hε
  have hεpos : 0 < ε := div_pos hδ₀pos (by linarith)
  have hεK : ∀ w ∈ V, ∀ g ∈ V, ε * (Ψ w - Ψ g) < δ₀ := by
    intro w hw g hg
    have h1 : Ψ w - Ψ g ≤ 2 * K := by
      have := hKle w hw; have := hKle g hg
      have := le_abs_self (Ψ w); have := neg_abs_le (Ψ g); linarith
    calc ε * (Ψ w - Ψ g) ≤ ε * (2 * K) := mul_le_mul_of_nonneg_left h1 hεpos.le
      _ < δ₀ := by
        rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  have hΦ : ∀ u, (ψ + ε • Ψ) u = ψ u + ε * Ψ u := fun u => rfl
  refine ⟨ψ + ε • Ψ, ?_⟩
  obtain ⟨g₀, hg₀⟩ := Proof.exposedFace_nonempty ⟨f₀, hf₀⟩ Ψ
  have hg₀F : g₀ ∈ F := exposedFace_subset F Ψ hg₀
  ext w
  unfold exposedFace
  simp only [Finset.mem_filter, hΦ]
  constructor
  · rintro ⟨hwV, hmax⟩
    have hwF : w ∈ F := by
      by_contra hwF
      have h1 := hmax g₀ (hfF g₀ hg₀F).1
      have h2 := hδ₀le w (Finset.mem_sdiff.mpr ⟨hwV, hwF⟩)
      have h3 := hεK w hwV g₀ (hfF g₀ hg₀F).1
      rw [hconst g₀ hg₀F] at h1
      nlinarith
    have hFF : w ∈ F := hwF
    rw [hFdef] at hwF
    refine ⟨hwF, fun u hu => ?_⟩
    have huF : u ∈ F := by rw [hFdef]; exact hu
    have h1 := hmax u (hfF u huF).1
    rw [hconst u huF, hconst w hFF] at h1
    have : ε * Ψ u ≤ ε * Ψ w := by linarith
    exact le_of_mul_le_mul_left this hεpos
  · rintro ⟨hwF, hmaxF⟩
    have hwF' : w ∈ F := by rw [hFdef]; exact hwF
    refine ⟨(hfF w hwF').1, fun u hu => ?_⟩
    by_cases huF : u ∈ F
    · rw [hconst u huF, hconst w hwF']
      have := hmaxF u (by rw [hFdef] at huF; exact huF)
      nlinarith
    · have h2 := hδ₀le u (Finset.mem_sdiff.mpr ⟨hu, huF⟩)
      have h3 := hεK u hu w (hfF w hwF').1
      rw [hconst w hwF']
      linarith

variable [FiniteDimensional ℝ E]

/-- The relative-interior property of a point whose minimal face is all of `W`: every direction
of the affine hull of `W` can be followed for a positive length within `conv W`. -/
theorem exists_add_smul_mem {W : Finset E} {y : E} (hy : y ∈ convexHull ℝ (↑W : Set E))
    (hmin : minFace W y = W) {d : E} (hd : d ∈ vectorSpan ℝ (↑W : Set E)) :
    ∃ ε : ℝ, 0 < ε ∧ y + ε • d ∈ convexHull ℝ (↑W : Set E) := by
  classical
  have hpush : ∀ w ∈ W, ∃ γ : ℝ, 0 < γ ∧ (1 + γ) • y - γ • w ∈ convexHull ℝ (↑W : Set E) :=
    fun w hw => push_away hy (by rw [hmin]; exact hw)
  choose! γ hγ using hpush
  have hyA : y ∈ affineSpan ℝ (↑W : Set E) := convexHull_subset_affineSpan _ hy
  set U := W.image (fun w => w - y) with hU
  have hspan : vectorSpan ℝ (↑W : Set E) = Submodule.span ℝ (↑U : Set E) := by
    rw [← vectorSpan_insert_eq_vectorSpan hyA,
      vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_insert y _), Set.image_insert_eq, vsub_self,
      Submodule.span_insert_zero, hU, Finset.coe_image]
    rfl
  rw [hspan] at hd
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hd
  have hWne : W.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hy
    exact hy
  have hd' : d = ∑ w ∈ W, c (w - y) • (w - y) := by
    rw [← hc, hU, Finset.sum_image (fun a _ b _ h => sub_left_injective h)]
  set N := (W.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hWne.card_pos
  set ε := W.inf' hWne (fun w => min 1 (γ w) / (N * (|c (w - y)| + 1))) with hε
  have hεpos : 0 < ε := by
    rw [hε, Finset.lt_inf'_iff]
    intro w hw
    exact div_pos (lt_min one_pos (hγ w hw).1) (by positivity)
  have hεle : ∀ w ∈ W, N * ε * |c (w - y)| ≤ min 1 (γ w) := by
    intro w hw
    have h1 : ε ≤ min 1 (γ w) / (N * (|c (w - y)| + 1)) := Finset.inf'_le _ hw
    have h2 : 0 < N * (|c (w - y)| + 1) := by positivity
    rw [le_div_iff₀ h2] at h1
    have h3 : 0 ≤ min 1 (γ w) := le_min zero_le_one (hγ w hw).1.le
    nlinarith [abs_nonneg (c (w - y)), hεpos]
  refine ⟨ε, hεpos, ?_⟩
  have hmem : ∀ w ∈ W, y + (N * ε * c (w - y)) • (w - y) ∈ convexHull ℝ (↑W : Set E) := by
    intro w hw
    set t := N * ε * c (w - y) with ht
    have hwC : w ∈ convexHull ℝ (↑W : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)
    have habs : |t| ≤ min 1 (γ w) := by
      rw [ht, abs_mul, abs_of_pos (by positivity : 0 < N * ε)]; exact hεle w hw
    rcases le_total 0 t with h0 | h0
    · exact (convex_convexHull ℝ _).add_smul_sub_mem hy hwC
        ⟨h0, (le_abs_self t).trans (habs.trans (min_le_left _ _))⟩
    · have hγpos := (hγ w hw).1
      have hs : -t / γ w ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (by linarith) hγpos.le, ?_⟩
        rw [div_le_one hγpos]
        have := (neg_le_abs t).trans (habs.trans (min_le_right _ _))
        linarith
      have h2 := (convex_convexHull ℝ _).add_smul_sub_mem hy (hγ w hw).2 hs
      convert h2 using 1
      have e1 : (1 + γ w) • y - γ w • w - y = γ w • (y - w) := by module
      rw [e1, smul_smul, div_mul_cancel₀ _ hγpos.ne']
      module
  have hsum := (convex_convexHull ℝ (↑W : Set E)).sum_mem (t := W) (w := fun _ => 1 / N)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp) hmem
  convert hsum using 1
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_const, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← hN, mul_one_div_cancel hNpos.ne', one_smul, hd',
    Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [smul_smul]
  congr 1
  field_simp

/-- The point where the segment from `a ∈ aff W \ conv W` to `b ∈ conv W` enters `conv W` lies in
a proper face of `conv W`. -/
theorem first_point {W : Finset E} {a b : E} (ha : a ∈ affineSpan ℝ (↑W : Set E))
    (haW : a ∉ convexHull ℝ (↑W : Set E)) (hb : b ∈ convexHull ℝ (↑W : Set E)) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ a + s • (b - a) ∈ convexHull ℝ (↑W : Set E) ∧
      minFace W (a + s • (b - a)) ≠ W := by
  set C := convexHull ℝ (↑W : Set E) with hC
  have hCc : IsClosed C := (Set.Finite.isCompact_convexHull (𝕜 := ℝ) W.finite_toSet).isClosed
  set T := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ a + s • (b - a) ∈ C} with hT
  have hTc : IsClosed T :=
    isClosed_Icc.inter (hCc.preimage (continuous_const.add (continuous_id.smul continuous_const)))
  have h1 : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by rw [one_smul, add_sub_cancel]; exact hb⟩
  have hbdd : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1⟩ hbdd
  have hs₀pos : 0 < s₀ := by
    rcases eq_or_lt_of_le hs₀T.1.1 with h | h
    · exfalso
      apply haW
      have := hs₀T.2
      rw [← h, zero_smul, add_zero] at this
      exact this
    · exact h
  refine ⟨s₀, hs₀pos, hs₀T.1.2, hs₀T.2, fun hmin => ?_⟩
  have hd : a - b ∈ vectorSpan ℝ (↑W : Set E) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction ha (convexHull_subset_affineSpan _ hb)
  obtain ⟨ε, hε, hεC⟩ := exists_add_smul_mem hs₀T.2 hmin hd
  set ε' := min ε s₀ with hε'
  have hε'pos : 0 < ε' := lt_min hε hs₀pos
  have hmem : a + (s₀ - ε') • (b - a) ∈ C := by
    have h2 := (convex_convexHull ℝ (↑W : Set E)).add_smul_sub_mem hs₀T.2 hεC (t := ε' / ε)
      ⟨by positivity, by rw [div_le_one hε]; exact min_le_left _ _⟩
    convert h2 using 1
    rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hε.ne']
    module
  have : s₀ ≤ s₀ - ε' :=
    csInf_le hbdd ⟨⟨by linarith [min_le_right ε s₀], by linarith [hs₀T.1.2]⟩, hmem⟩
  linarith

end Faces

section Reduce

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **The reduction step.** If `a ∈ aff F` lies outside `conv F` and `q ∈ conv (V \ F)`, a proper
face `G` with fewer points carries `z ∈ aff G` and `q' ∈ conv (V \ G)` with
`‖z - q'‖ = (1 - τ) ‖a - q‖` for some `τ > 0`. -/
theorem reduce_step {V : Finset E} {ψ : StrongDual ℝ E} (hF : exposedFace V ψ ≠ V) {a q : E}
    (ha : a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E))
    (haF : a ∉ convexHull ℝ (↑(exposedFace V ψ) : Set E))
    (hq : q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E)) :
    ∃ Φ : StrongDual ℝ E, exposedFace V Φ ≠ V ∧
      (exposedFace V Φ).card < (exposedFace V ψ).card ∧
      ∃ τ : ℝ, 0 < τ ∧ ∃ z ∈ affineSpan ℝ (↑(exposedFace V Φ) : Set E),
        ∃ q' ∈ convexHull ℝ (↑(V \ exposedFace V Φ) : Set E), ‖z - q'‖ = (1 - τ) * ‖a - q‖ := by
  classical
  set W := exposedFace V ψ with hW
  have hWV : W ⊆ V := exposedFace_subset V ψ
  have hWne : W.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, AffineSubspace.span_empty] at ha
    exact AffineSubspace.notMem_bot ℝ E a ha
  have hbary : ∀ U : Finset E, U.Nonempty →
      (1 / (U.card : ℝ)) • ∑ w ∈ U, w ∈ convexHull ℝ (↑U : Set E) := by
    intro U hU
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
    rw [Finset.smul_sum]
    exact (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
      (fun w hw => subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
  set n := (W.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hWne.card_pos
  set b := (1 / n) • ∑ w ∈ W, w with hb
  have hbC : b ∈ convexHull ℝ (↑W : Set E) := hbary W hWne
  obtain ⟨s, hs0, hs1, hp'C, hG⟩ := first_point ha haF hbC
  set p' := a + s • (b - a) with hp'
  set G := minFace W p' with hGdef
  obtain ⟨Ψ, -, hGΨ⟩ := minFace_exposed hp'C
  obtain ⟨Φ, hΦ⟩ := exists_exposedFace_eq V ψ Ψ
  have hΦG : exposedFace V Φ = G := by rw [hΦ, ← hW, hGdef, hGΨ]
  have hGW : G ⊆ W := by rw [hGdef]; unfold minFace; exact Finset.filter_subset _ _
  have hGss : G ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨hGW, hG⟩
  have hp'G : p' ∈ convexHull ℝ (↑G : Set E) := mem_convexHull_minFace hp'C
  have hGne : G.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hp'G
    exact hp'G
  have hWG : (W \ G).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact fun h => hG (Finset.Subset.antisymm hGW h)
  set m := (G.card : ℝ) with hm
  set k := ((W \ G).card : ℝ) with hk
  have hmpos : 0 < m := by rw [hm]; exact_mod_cast hGne.card_pos
  have hkpos : 0 < k := by rw [hk]; exact_mod_cast hWG.card_pos
  have hmk : m + k = n := by
    rw [hm, hk, hn, add_comm]; exact_mod_cast Finset.card_sdiff_add_card_eq_card hGW
  set g := (1 / m) • ∑ w ∈ G, w with hg
  set r := (1 / k) • ∑ w ∈ W \ G, w with hr
  have hgC : g ∈ convexHull ℝ (↑G : Set E) := hbary G hGne
  have hrC : r ∈ convexHull ℝ (↑(W \ G) : Set E) := hbary (W \ G) hWG
  have hbgr : b = (m / n) • g + (k / n) • r := by
    rw [hb, hg, hr, smul_smul, smul_smul, ← Finset.sum_sdiff hGW, smul_add, add_comm]
    congr 1 <;> congr 1 <;> field_simp
  set α := 1 - s * m / n with hα
  have hαpos : 0 < α := by
    have h1 : m < n := by linarith
    have h2 : s * m < n := by nlinarith
    rw [hα, sub_pos, div_lt_one hnpos]; exact h2
  set τ := α⁻¹ * (s * k / n) with hτ
  have hτpos : 0 < τ := mul_pos (inv_pos.mpr hαpos) (div_pos (mul_pos hs0 hkpos) hnpos)
  have hατ : α * τ = s * k / n := by rw [hτ, ← mul_assoc, mul_inv_cancel₀ hαpos.ne', one_mul]
  have hsk : s * k / n + s * m / n = s := by
    rw [← add_div, ← mul_add, add_comm k m, hmk, mul_div_assoc, div_self hnpos.ne',
      mul_one]
  have hτle : τ ≤ 1 := by
    have h1 : α * τ ≤ α * 1 := by
      rw [hατ, mul_one, hα]
      linarith
    exact le_of_mul_le_mul_left h1 hαpos
  set z := a + τ • (r - a) with hz
  have hα' : α = (1 - s) + s * k / n := by
    rw [hα]; linarith
  have hαz : α • z = (1 - s) • a + (s * k / n) • r := by
    rw [hz, smul_add, smul_smul, hατ, hα']
    module
  refine ⟨Φ, ?_, ?_, τ, hτpos, z, ?_, q + τ • (r - q), ?_, ?_⟩
  · rw [hΦG]
    intro h
    exact hF (Finset.Subset.antisymm hWV (h ▸ hGW))
  · rw [hΦG]; exact Finset.card_lt_card hGss
  · rw [hΦG]
    have hp'A : p' ∈ affineSpan ℝ (↑G : Set E) := convexHull_subset_affineSpan _ hp'G
    have hgA : g ∈ affineSpan ℝ (↑G : Set E) := convexHull_subset_affineSpan _ hgC
    have hkey : α • (z - p') = (s * m / n) • (p' - g) := by
      rw [smul_sub, hαz, hp', hbgr, hα]
      module
    have hdir : z - p' ∈ (affineSpan ℝ (↑G : Set E)).direction := by
      have h1 : z - p' = α⁻¹ • ((s * m / n) • (p' - g)) := by
        rw [← hkey, smul_smul, inv_mul_cancel₀ hαpos.ne', one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (AffineSubspace.vsub_mem_direction hp'A hgA))
    have := AffineSubspace.vadd_mem_of_mem_direction hdir hp'A
    rwa [vadd_eq_add, sub_add_cancel] at this
  · rw [hΦG]
    have hsub1 : (↑(V \ W) : Set E) ⊆ ↑(V \ G) := by
      intro x hx
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx ⊢
      exact ⟨hx.1, fun h => hx.2 (hGW h)⟩
    have hsub2 : (↑(W \ G) : Set E) ⊆ ↑(V \ G) := by
      intro x hx
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx ⊢
      exact ⟨hWV hx.1, hx.2⟩
    exact (convex_convexHull ℝ _).add_smul_sub_mem (convexHull_mono hsub1 hq)
      (convexHull_mono hsub2 hrC) ⟨hτpos.le, hτle⟩
  · have e : z - (q + τ • (r - q)) = (1 - τ) • (a - q) := by rw [hz]; module
    rw [e, norm_smul, Real.norm_of_nonneg (by linarith)]

open Classical in
/-- **Corollary 4.4**, the hard inequality: the facial distance is at most the affine pyramidal
width. -/
theorem facial_le_affine (V : Finset E) : facialDistance V ≤ affinePyramidalWidth V := by
  classical
  have key : ∀ N : ℕ, ∀ ψ : StrongDual ℝ E, (exposedFace V ψ).card ≤ N → exposedFace V ψ ≠ V →
      ∀ a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E),
        ∀ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), facialDistance V ≤ ‖a - q‖ := by
    intro N
    induction N with
    | zero =>
      intro ψ hcard _ a ha
      have h0 : exposedFace V ψ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      rw [h0, Finset.coe_empty, AffineSubspace.span_empty] at ha
      exact absurd ha (AffineSubspace.notMem_bot ℝ E a)
    | succ N ih =>
      intro ψ hcard hF a ha q hq
      by_cases haF : a ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E)
      · exact Proof.facialDistance_le hF haF hq
      · obtain ⟨Φ, hΦ, hlt, τ, hτ, z, hz, q', hq', hzq⟩ := reduce_step hF ha haF hq
        have h1 := ih Φ (by omega) hΦ z hz q' hq'
        rw [hzq] at h1
        nlinarith [norm_nonneg (a - q)]
  set S : Set ℝ := {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
    ∃ a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E),
      ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖a - q‖} with hS
  have hwidth : affinePyramidalWidth V = sInf S := rfl
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · -- no proper face: both widths vanish
    have hnone : ∀ ψ : StrongDual ℝ E, exposedFace V ψ = V := by
      intro ψ
      by_contra hF
      have hVne : V.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        exact hF (by rw [h]; exact Finset.subset_empty.mp (h ▸ exposedFace_subset V ψ))
      obtain ⟨p, hp⟩ := Proof.exposedFace_nonempty hVne ψ
      obtain ⟨q, hq⟩ := sdiff_exposedFace_nonempty hF
      have : ‖p - q‖ ∈ S := ⟨ψ, hF, p, subset_affineSpan ℝ _ (Finset.mem_coe.mpr hp), q,
        subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), rfl⟩
      rw [hS0] at this
      exact this
    have hfd : facialDistance V = 0 := by
      unfold facialDistance
      convert Real.sInf_empty
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ψ, hF, -⟩
      exact hF (hnone ψ)
    rw [hfd]
    exact affinePyramidalWidth_nonneg V
  · rw [hwidth]
    exact le_csInf hSne (fun r ⟨ψ, hF, a, ha, q, hq, hr⟩ => hr ▸ key _ ψ le_rfl hF a ha q hq)

/-- **Corollary 4.4**: the affine pyramidal width equals the facial distance. -/
theorem affine_eq_facial (V : Finset E) : affinePyramidalWidth V = facialDistance V :=
  le_antisymm (affine_le_facial V) (facial_le_affine V)

end Reduce

section Relint

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **Lemma 4.3**: a point of the affine hull realizing the affine pyramidal width lies in the
relative interior of its face. -/
theorem relint_of_width {V : Finset E} {ψ : StrongDual ℝ E} (hF : exposedFace V ψ ≠ V) {a q : E}
    (ha : a ∈ affineSpan ℝ (↑(exposedFace V ψ) : Set E))
    (hq : q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E))
    (hmin : ‖a - q‖ = affinePyramidalWidth V) :
    a ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E) ∧
      minFace (exposedFace V ψ) a = exposedFace V ψ := by
  classical
  set F := exposedFace V ψ with hFdef
  have hFV : F ⊆ V := exposedFace_subset V ψ
  have hVne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hF (by rw [hFdef, h]; exact Finset.subset_empty.mp (h ▸ exposedFace_subset V ψ))
  obtain ⟨f₀, hf₀⟩ := Proof.exposedFace_nonempty hVne ψ
  have hfF : ∀ w ∈ F, w ∈ V ∧ ∀ u ∈ V, ψ u ≤ ψ w := fun w hw => by
    rw [hFdef] at hw
    unfold exposedFace at hw
    exact Finset.mem_filter.mp hw
  -- the distance is positive: `ψ` is constant on `aff F` and smaller on `conv (V \ F)`
  have hd : 0 < ‖a - q‖ := by
    have hψa : ψ a = ψ f₀ := apply_eq_of_mem_affineSpan ψ (fun w hw => le_antisymm
      ((hfF f₀ hf₀).2 w (hfF w (Finset.mem_coe.mp hw)).1)
      ((hfF w (Finset.mem_coe.mp hw)).2 f₀ (hfF f₀ hf₀).1)) ha
    obtain ⟨u, hu⟩ := sdiff_exposedFace_nonempty hF
    obtain ⟨w₀, hw₀, hmax⟩ := (V \ F).exists_max_image ψ ⟨u, hu⟩
    have hclt : ψ w₀ < ψ f₀ := by
      rw [Finset.mem_sdiff] at hw₀
      by_contra hle
      apply hw₀.2
      rw [hFdef]
      unfold exposedFace
      exact Finset.mem_filter.mpr ⟨hw₀.1, fun v hv => ((hfF f₀ hf₀).2 v hv).trans (not_lt.mp hle)⟩
    have hψq : ψ q ≤ ψ w₀ := le_on_hull ψ hmax q hq
    have hne : a ≠ q := fun h => by rw [h] at hψa; linarith
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- `a` lies in `conv F`
  have haF : a ∈ convexHull ℝ (↑F : Set E) := by
    by_contra haF
    obtain ⟨Φ, hΦ, -, τ, hτ, z, hz, q', hq', hzq⟩ := reduce_step hF ha haF hq
    have h1 := affinePyramidalWidth_le hΦ hz hq'
    rw [hzq, ← hmin] at h1
    nlinarith
  refine ⟨haF, ?_⟩
  -- `a` lies in no proper face of `conv F`
  by_contra hne
  set G := minFace F a with hGdef
  obtain ⟨Ψ, -, hGΨ⟩ := minFace_exposed haF
  obtain ⟨Φ, hΦ⟩ := exists_exposedFace_eq V ψ Ψ
  have hΦG : exposedFace V Φ = G := by rw [hΦ, ← hFdef, hGdef, hGΨ]
  have hGF : G ⊆ F := by rw [hGdef]; unfold minFace; exact Finset.filter_subset _ _
  obtain ⟨v, hvF, hvG⟩ : ∃ v ∈ F, v ∉ G := by
    by_contra h
    push Not at h
    exact hne (Finset.Subset.antisymm hGF h)
  have hGV : exposedFace V Φ ≠ V := by
    rw [hΦG]; intro h; exact hF (Finset.Subset.antisymm hFV (h ▸ hGF))
  -- `a` minimizes the distance to `q` over `aff F`, so `a - q` is orthogonal to `v - a`
  have hvA : v ∈ affineSpan ℝ (↑F : Set E) := subset_affineSpan ℝ _ (Finset.mem_coe.mpr hvF)
  have horth : inner ℝ (a - q) (v - a) = 0 := by
    have hline : ∀ t : ℝ, ‖a - q‖ ^ 2 ≤ ‖a - q‖ ^ 2 + 2 * t * inner ℝ (a - q) (v - a) +
        t ^ 2 * ‖v - a‖ ^ 2 := by
      intro t
      have hmem : t • (v - a) + a ∈ affineSpan ℝ (↑F : Set E) := by
        have := AffineSubspace.vadd_mem_of_mem_direction
          (Submodule.smul_mem _ t (AffineSubspace.vsub_mem_direction hvA ha)) ha
        rwa [vsub_eq_sub, vadd_eq_add] at this
      have h1 := affinePyramidalWidth_le hF hmem hq
      rw [← hmin] at h1
      have h2 : ‖t • (v - a) + a - q‖ ^ 2 = ‖a - q‖ ^ 2 + 2 * t * inner ℝ (a - q) (v - a) +
          t ^ 2 * ‖v - a‖ ^ 2 := by
        rw [show t • (v - a) + a - q = (a - q) + t • (v - a) by abel, norm_add_sq_real,
          inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      rw [← h2]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    set X := inner ℝ (a - q) (v - a) with hX
    set Y := ‖v - a‖ ^ 2 with hY
    have hY0 : 0 ≤ Y := by positivity
    have h1 := hline (-X / (Y + 1))
    have h2 : X ^ 2 * (Y + 2) ≤ 0 := by
      have hpos : 0 < Y + 1 := by linarith
      field_simp at h1
      nlinarith
    have : X ^ 2 ≤ 0 := by nlinarith [sq_nonneg X]
    nlinarith [sq_nonneg X]
  -- moving `q` toward `v` brings it closer to `a`, contradicting minimality
  set d := ‖a - q‖ with hdd
  set e := ‖v - a‖ with he
  set σ := d ^ 2 / (d ^ 2 + e ^ 2) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by rw [hσ, div_le_one (by positivity)]; nlinarith [sq_nonneg e]
  have hq'C : q + σ • (v - q) ∈ convexHull ℝ (↑(V \ exposedFace V Φ) : Set E) := by
    rw [hΦG]
    have hsub1 : (↑(V \ F) : Set E) ⊆ ↑(V \ G) := by
      intro x hx
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx ⊢
      exact ⟨hx.1, fun h => hx.2 (hGF h)⟩
    have hvVG' : v ∈ (↑(V \ G) : Set E) := by
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      exact ⟨hFV hvF, hvG⟩
    have hvVG : v ∈ convexHull ℝ (↑(V \ G) : Set E) := subset_convexHull ℝ _ hvVG'
    exact (convex_convexHull ℝ _).add_smul_sub_mem (convexHull_mono hsub1 hq) hvVG ⟨hσ0.le, hσ1⟩
  have haG : a ∈ affineSpan ℝ (↑(exposedFace V Φ) : Set E) := by
    rw [hΦG]; exact convexHull_subset_affineSpan _ (mem_convexHull_minFace haF)
  have h1 := affinePyramidalWidth_le hGV haG hq'C
  rw [← hmin] at h1
  have h2 : ‖a - (q + σ • (v - q))‖ ^ 2 = d ^ 2 - σ * d ^ 2 := by
    have e1 : a - (q + σ • (v - q)) = (1 - σ) • (a - q) - σ • (v - a) := by module
    rw [e1, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      horth, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - σ),
      abs_of_pos hσ0, ← hdd, ← he]
    simp only [RCLike.conj_to_real, mul_zero, sub_zero]
    have hsum : σ * (d ^ 2 + e ^ 2) = d ^ 2 := by
      rw [hσ]; field_simp
    nlinarith [hsum]
  have h3 : ‖a - (q + σ • (v - q))‖ ^ 2 < d ^ 2 := by
    rw [h2]; nlinarith [mul_pos hσ0 (pow_pos hd 2)]
  have h4 : d ^ 2 ≤ ‖a - (q + σ • (v - q))‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith

end Relint

section Product

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-- **Theorem 4.5**: the pyramidal width of a product of two polytopes. -/
theorem pyramidal_width_product {V₁ : Finset E₁} {V₂ : Finset E₂} (h1 : 1 < V₁.card)
    (h2 : 1 < V₂.card) :
    facialDistance (productVertices V₁ V₂) =
      Real.sqrt (facialDistance V₁ ^ 2 * facialDistance V₂ ^ 2 /
        (facialDistance V₁ ^ 2 + facialDistance V₂ ^ 2)) := by
  apply le_antisymm (product_width_upper_bound h1 h2)
  have hV₁ : V₁.Nonempty := Finset.card_pos.mp (by omega)
  have hV₂ : V₂.Nonempty := Finset.card_pos.mp (by omega)
  have := product_width_lower_bound hV₁ hV₂
  rwa [affine_eq_facial V₁, affine_eq_facial V₂] at this

end Product

namespace Proof

theorem affine_width_relint : AffineWidthRelint.{u} := by
  intro E _ _ _ V ψ a q hF ha hq hmin
  exact relint_of_width hF ha hq hmin

theorem affine_width_eq : AffineWidthEq.{u} := fun V => affine_eq_facial V

theorem product_width_eq : ProductWidthEq.{u} := by
  intro E₁ E₂ _ _ _ _ _ _ V₁ V₂ h1 h2
  exact pyramidal_width_product h1 h2

end Proof

end Lemmata.FWProduct
