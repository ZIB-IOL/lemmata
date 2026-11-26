module

public import Lemmata.FrankWolfe.Polytope.Cone
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Faces of polytopes

For a finite set `V`, the exposed face of `conv V` for a functional `ψ` has the vertices of `V` that
maximize `ψ`. The minimal face of a point `y` has the vertices that lie in every exposed face whose
functional is maximized at `y`. A vertex of the minimal face of `y` can be pushed away from: the
point `(1 + γ) y - γ v` stays in `conv V` for some `γ > 0` (a consequence of the Farkas lemma).
-/

namespace Lemmata.FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem apply_le_of_mem_convexHull {V : Finset E} (ψ : StrongDual ℝ E) {v : E}
    (hv : ∀ u ∈ V, ψ u ≤ ψ v) {y : E} (hy : y ∈ convexHull ℝ (↑V : Set E)) : ψ y ≤ ψ v := by
  have hsub : (↑V : Set E) ⊆ {z | ψ z ≤ ψ v} := fun u hu => hv u hu
  exact convexHull_min hsub (convex_halfSpace_le ψ.toLinearMap.isLinear _) hy

/-- **Pushing away from a vertex of the minimal face.** -/
theorem push_away [FiniteDimensional ℝ E] {V : Finset E} {y v : E}
    (hy : y ∈ convexHull ℝ (↑V : Set E)) (hv : v ∈ minFace V y) :
    ∃ γ : ℝ, 0 < γ ∧ (1 + γ) • y - γ • v ∈ convexHull ℝ (↑V : Set E) := by
  classical
  set G := V.image (fun w => w - y) with hG
  by_cases hcone : y - v ∈ coneHull G
  · obtain ⟨c, hc, hyv⟩ := hcone
    set s := ∑ g ∈ G, c g with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg hc
    rcases eq_or_lt_of_le hs0 with hs0' | hspos
    · -- all coefficients vanish, so `v = y`
      have hc0 : ∀ g ∈ G, c g = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hc).mp hs0'.symm
      have hvy : y - v = 0 := by
        rw [hyv]; exact Finset.sum_eq_zero (fun g hg => by rw [hc0 g hg, zero_smul])
      refine ⟨1, one_pos, ?_⟩
      have : v = y := (sub_eq_zero.mp hvy).symm
      rw [this, ← sub_smul]
      simpa using hy
    · set z : E := ∑ g ∈ G, (c g / s) • (g + y) with hz
      have hzV : z ∈ convexHull ℝ (↑V : Set E) := by
        refine (convex_convexHull ℝ _).sum_mem (fun g hg => div_nonneg (hc g hg) hs0) ?_ ?_
        · rw [← Finset.sum_div, ← hs, div_self hspos.ne']
        · intro g hg
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hg
          exact subset_convexHull ℝ _ (by simpa using hw)
      have hz' : z = (1 / s) • (y - v) + y := by
        rw [hz, hyv]
        simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
        congr 1
        · exact Finset.sum_congr rfl (fun g _ => by congr 1; ring)
        · rw [← Finset.sum_smul, ← Finset.sum_div, ← hs, div_self hspos.ne', one_smul]
      have h1 : s / (1 + s) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      refine ⟨1 / (1 + s), by positivity, ?_⟩
      have hcomb := (convex_convexHull ℝ (↑V : Set E)) hy hzV (sub_nonneg.mpr h1)
        (by positivity : (0 : ℝ) ≤ s / (1 + s)) (by ring)
      convert hcomb using 1
      rw [hz']
      match_scalars <;> field_simp
      ring
  · obtain ⟨ψ, hψG, hψ⟩ := farkas G hcone
    have hmax : ∀ u ∈ V, ψ u ≤ ψ y := by
      intro u hu
      have := hψG (u - y) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      rw [map_sub] at this
      linarith
    have hvmax := (Finset.mem_filter.mp hv).2 ψ hmax
    have := apply_le_of_mem_convexHull ψ hvmax hy
    rw [map_sub] at hψ
    linarith

theorem exposedFace_subset (V : Finset E) (ψ : StrongDual ℝ E) : exposedFace V ψ ⊆ V := by
  classical
  unfold exposedFace
  exact Finset.filter_subset _ _

theorem mem_convexHull_exposedFace_iff {V : Finset E} (ψ : StrongDual ℝ E) {y : E}
    (hy : y ∈ convexHull ℝ (↑V : Set E)) :
    y ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E) ↔ ∀ u ∈ V, ψ u ≤ ψ y := by
  classical
  constructor
  · intro hyF u hu
    have hsub : (↑(exposedFace V ψ) : Set E) ⊆ {z | ψ u ≤ ψ z} := fun w hw => by
      simp only [exposedFace, Finset.coe_filter, Set.mem_ofPred_eq] at hw
      exact hw.2 u hu
    exact convexHull_min hsub (convex_halfSpace_ge ψ.toLinearMap.isLinear _) hyF
  · intro hmax
    obtain ⟨c, hc0, hc1, hcy⟩ := Finset.mem_convexHull'.mp hy
    have hzero : ∀ w ∈ V, c w * (ψ y - ψ w) = 0 := by
      have hsum : ∑ w ∈ V, c w * (ψ y - ψ w) = 0 := by
        have e1 : ∑ w ∈ V, c w * ψ w = ψ y := by
          rw [← hcy, map_sum]; simp [map_smul, smul_eq_mul]
        simp only [mul_sub, Finset.sum_sub_distrib, e1, ← Finset.sum_mul, hc1, one_mul, sub_self]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun w hw =>
        mul_nonneg (hc0 w hw) (by linarith [hmax w hw]))).mp hsum
    have hc' : ∀ w ∈ V, w ∉ exposedFace V ψ → c w = 0 := by
      intro w hw hwF
      have hne : ψ y - ψ w ≠ 0 := by
        intro h
        apply hwF
        simp only [exposedFace, Finset.mem_filter]
        exact ⟨hw, fun u hu => by linarith [hmax u hu]⟩
      exact (mul_eq_zero.mp (hzero w hw)).resolve_right hne
    rw [Finset.mem_convexHull']
    refine ⟨c, fun w hw => hc0 w (exposedFace_subset V ψ hw), ?_, ?_⟩
    · exact (Finset.sum_subset (exposedFace_subset V ψ) (fun w hw hwf => hc' w hw hwf)).trans hc1
    · exact (Finset.sum_subset (exposedFace_subset V ψ)
        (fun w hw hwf => by rw [hc' w hw hwf, zero_smul])).trans hcy

open Classical in
/-- Two functionals maximized at `y` add to a functional maximized at `y` whose face is the
intersection of their faces. -/
theorem exposedFace_add {V : Finset E} {y : E} (hy : y ∈ convexHull ℝ (↑V : Set E))
    {ψ₁ ψ₂ : StrongDual ℝ E} (h₁ : ∀ u ∈ V, ψ₁ u ≤ ψ₁ y) (h₂ : ∀ u ∈ V, ψ₂ u ≤ ψ₂ y) :
    (∀ u ∈ V, (ψ₁ + ψ₂) u ≤ (ψ₁ + ψ₂) y) ∧
      exposedFace V (ψ₁ + ψ₂) = exposedFace V ψ₁ ∩ exposedFace V ψ₂ := by
  classical
  -- the maxima over `V` are attained at vertices of the faces, so they equal the values at `y`
  have hF₁ := (mem_convexHull_exposedFace_iff ψ₁ hy).mpr h₁
  have hF₂ := (mem_convexHull_exposedFace_iff ψ₂ hy).mpr h₂
  have hval : ∀ (ψ : StrongDual ℝ E), (∀ u ∈ V, ψ u ≤ ψ y) →
      ∀ w ∈ exposedFace V ψ, ψ w = ψ y := by
    intro ψ hψ w hw
    simp only [exposedFace, Finset.mem_filter] at hw
    have hle := hψ w hw.1
    have hge : ψ y ≤ ψ w := apply_le_of_mem_convexHull ψ hw.2 hy
    linarith
  refine ⟨fun u hu => by
    simp only [add_apply]; linarith [h₁ u hu, h₂ u hu], ?_⟩
  ext w
  simp only [exposedFace, Finset.mem_inter, Finset.mem_filter, add_apply]
  constructor
  · rintro ⟨hw, hmax⟩
    -- `(ψ₁ + ψ₂) w ≥ (ψ₁ + ψ₂) y` forces both values to be maximal
    obtain ⟨w₁, hw₁⟩ : (exposedFace V ψ₁).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.coe_empty, convexHull_empty] at hF₁
      exact hF₁
    have hy₁ : ψ₁ y ≤ ψ₁ w + (ψ₂ w - ψ₂ y) := by
      have := hmax
      have hb : ψ₁ (w) + ψ₂ w ≥ ψ₁ y + ψ₂ y := by
        have hconv := apply_le_of_mem_convexHull (ψ₁ + ψ₂) (fun u hu => by
          simp only [add_apply]; exact hmax u hu) hy
        simpa using hconv
      linarith
    have hw1 : ψ₁ y ≤ ψ₁ w := by linarith [h₂ w hw]
    have hw2 : ψ₂ y ≤ ψ₂ w := by
      have hb : ψ₁ w + ψ₂ w ≥ ψ₁ y + ψ₂ y := by
        have hconv := apply_le_of_mem_convexHull (ψ₁ + ψ₂) (fun u hu => by
          simp only [add_apply]; exact hmax u hu) hy
        simpa using hconv
      linarith [h₁ w hw]
    exact ⟨⟨hw, fun u hu => (h₁ u hu).trans hw1⟩, ⟨hw, fun u hu => (h₂ u hu).trans hw2⟩⟩
  · rintro ⟨⟨hw, hm₁⟩, ⟨-, hm₂⟩⟩
    exact ⟨hw, fun u hu => add_le_add (hm₁ u hu) (hm₂ u hu)⟩

/-- The minimal face of a point of `conv V` is an exposed face, for a functional maximized at `y`.
-/
theorem minFace_exposed {V : Finset E} {y : E} (hy : y ∈ convexHull ℝ (↑V : Set E)) :
    ∃ Ψ : StrongDual ℝ E, (∀ u ∈ V, Ψ u ≤ Ψ y) ∧ minFace V y = exposedFace V Ψ := by
  classical
  set fam := V.powerset.filter (fun F => ∃ ψ : StrongDual ℝ E, (∀ u ∈ V, ψ u ≤ ψ y) ∧
    exposedFace V ψ = F) with hfam
  have hchoose : ∀ F ∈ fam, ∃ ψ : StrongDual ℝ E, (∀ u ∈ V, ψ u ≤ ψ y) ∧ exposedFace V ψ = F :=
    fun F hF => (Finset.mem_filter.mp hF).2
  choose! ψF hψF using hchoose
  have key : ∀ T ⊆ fam, (∀ u ∈ V, (∑ F ∈ T, ψF F) u ≤ (∑ F ∈ T, ψF F) y) ∧
      exposedFace V (∑ F ∈ T, ψF F) = V.filter (fun w => ∀ F ∈ T, w ∈ F) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun u _ => by simp, ?_⟩
      ext w
      simp [exposedFace]
    | insert F T hFT ih =>
      intro hsub
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hF := hψF F (hsub (Finset.mem_insert_self _ _))
      rw [Finset.sum_insert hFT]
      obtain ⟨h1, h2⟩ := exposedFace_add hy hF.1 ih1
      refine ⟨h1, ?_⟩
      rw [h2, hF.2, ih2]
      have hFV : F ⊆ V := hF.2 ▸ exposedFace_subset V (ψF F)
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
      constructor
      · rintro ⟨hwF, hwV, hall⟩; exact ⟨hwV, hwF, hall⟩
      · rintro ⟨hwV, hwF, hall⟩; exact ⟨hwF, hwV, hall⟩
  obtain ⟨hmax, hface⟩ := key fam (le_refl _)
  refine ⟨_, hmax, ?_⟩
  rw [hface]
  ext w
  simp only [minFace, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hall⟩
    refine ⟨hw, fun F hF => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := (Finset.mem_filter.mp hF).2
    unfold exposedFace
    exact Finset.mem_filter.mpr ⟨hw, hall ψ hψ⟩
  · rintro ⟨hw, hall⟩
    refine ⟨hw, fun ψ hψ => ?_⟩
    have hF : exposedFace V ψ ∈ fam :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (exposedFace_subset V ψ), ψ, hψ, rfl⟩
    have := hall _ hF
    unfold exposedFace at this
    exact (Finset.mem_filter.mp this).2

theorem mem_convexHull_minFace {V : Finset E} {y : E} (hy : y ∈ convexHull ℝ (↑V : Set E)) :
    y ∈ convexHull ℝ (↑(minFace V y) : Set E) := by
  obtain ⟨Ψ, hmax, hface⟩ := minFace_exposed hy
  rw [hface]
  exact (mem_convexHull_exposedFace_iff Ψ hy).mpr hmax

/-- A point lies in the relative interior of its minimal face: a functional that is maximized at `y`
over the minimal face of `y` is constant on that face. -/
theorem eq_of_mem_minFace_of_max [FiniteDimensional ℝ E] {V : Finset E} {y : E}
    (hy : y ∈ convexHull ℝ (↑V : Set E)) (ψ : StrongDual ℝ E)
    (hmax : ∀ w ∈ minFace V y, ψ w ≤ ψ y) : ∀ v ∈ minFace V y, ψ v = ψ y := by
  classical
  intro v hv
  obtain ⟨Ψ, hΨ, hface⟩ := minFace_exposed hy
  obtain ⟨γ, hγ, hyγ⟩ := push_away hy hv
  have hvF : v ∈ exposedFace V Ψ := hface ▸ hv
  have hvV : v ∈ V := exposedFace_subset V Ψ hvF
  have hΨv : Ψ v = Ψ y := by
    have h1 : Ψ v ≤ Ψ y := hΨ v hvV
    have h2 : Ψ y ≤ Ψ v := by
      unfold exposedFace at hvF
      exact apply_le_of_mem_convexHull Ψ (Finset.mem_filter.mp hvF).2 hy
    linarith
  have hΨγ : ∀ u ∈ V, Ψ u ≤ Ψ ((1 + γ) • y - γ • v) := by
    intro u hu
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hΨv]
    linarith [hΨ u hu]
  have hyγF : (1 + γ) • y - γ • v ∈ convexHull ℝ (↑(minFace V y) : Set E) := by
    rw [hface]; exact (mem_convexHull_exposedFace_iff Ψ hyγ).mpr hΨγ
  have hle := apply_le_of_mem_convexHull ψ hmax hyγF
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hle
  have := hmax v hv
  nlinarith

end Lemmata.FrankWolfe
