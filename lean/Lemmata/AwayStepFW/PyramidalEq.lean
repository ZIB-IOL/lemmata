module

public import Lemmata.AwayStepFW.FacialDistance
public import Lemmata.AwayStepFW.FCFW
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Pointwise

@[expose] public section

/-!
# Pyramidal width equals facial distance (Proposition 2.31)

The upper bound: separate the open `δ`-neighbourhood of the minimal face of a closest point from the
convex hull of the remaining vertices, and evaluate the scaling inequality at the closest pair.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

open Pointwise

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separating the open `δ`-neighbourhood of a convex set `A` from a convex set `B` at distance at
least `δ`: `f a + ‖f‖ δ ≤ f b`. -/
theorem separate_neighbourhood {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ a ∈ A, ∀ b ∈ B, δ ≤ ‖a - b‖) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, f a + ‖f‖ * δ ≤ f b := by
  have hopen : IsOpen (A + Metric.ball (0 : E) δ) := Metric.isOpen_ball.add_left
  have hconv : Convex ℝ (A + Metric.ball (0 : E) δ) := hA.add (convex_ball 0 δ)
  have hdisj : Disjoint (A + Metric.ball (0 : E) δ) B := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, u, hu, rfl⟩ hzB
    have := hfar a ha (a + u) hzB
    rw [mem_ball_zero_iff] at hu
    rw [sub_add_cancel_left, norm_neg] at this
    linarith
  obtain ⟨f, u0, hfs, hft⟩ := geometric_hahn_banach_open hconv hopen hB hdisj
  have hfa : ∀ a ∈ A, f a + ‖f‖ * δ ≤ u0 := by
    intro a ha
    have hc : f a < u0 := by
      have := hfs (a + 0) ⟨a, ha, 0, Metric.mem_ball_self hδ, rfl⟩
      rwa [add_zero] at this
    set c := u0 - f a with hcdef
    have hc0 : 0 < c := by linarith
    have hbound : ∀ w : E, ‖w‖ = 1 → f w ≤ c / δ := by
      intro w hw
      by_contra hlt
      push Not at hlt
      have hfw : 0 < f w := lt_trans (div_pos hc0 hδ) hlt
      set s0 := c / f w with hs0
      have hs0pos : 0 < s0 := div_pos hc0 hfw
      have hs0δ : s0 < δ := by
        rw [hs0, div_lt_iff₀ hfw]
        rw [div_lt_iff₀ hδ] at hlt
        linarith
      have hmem : a + s0 • w ∈ A + Metric.ball (0 : E) δ := by
        refine ⟨a, ha, s0 • w, ?_, rfl⟩
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hs0pos.le, hw, mul_one]
        exact hs0δ
      have := hfs _ hmem
      rw [map_add, map_smul, smul_eq_mul, hs0, div_mul_cancel₀ _ hfw.ne'] at this
      linarith
    have hnorm : ‖f‖ ≤ c / δ := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hc0.le hδ.le) (fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, hbound w hw⟩
      have := hbound (-w) (by rw [norm_neg, hw])
      rw [map_neg] at this
      linarith
    have := mul_le_mul_of_nonneg_right hnorm hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  refine ⟨f, fun hf0 => ?_, fun a ha b hb => (hfa a ha).trans (hft b hb)⟩
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have h1 := hfs (a + 0) ⟨a, ha, 0, Metric.mem_ball_self hδ, rfl⟩
  have h2 := hft b hb
  rw [hf0] at h1 h2
  simp only [zero_apply] at h1 h2
  linarith

theorem exposedFace_nonempty {V : Finset E} (hV : V.Nonempty) (ψ : StrongDual ℝ E) :
    (exposedFace V ψ).Nonempty := by
  classical
  obtain ⟨w, hw, hmax⟩ := V.exists_max_image ψ hV
  exact ⟨w, by unfold exposedFace; exact Finset.mem_filter.mpr ⟨hw, hmax⟩⟩

open Classical in
/-- If a proper exposed face exists, the facial distance is attained and positive. -/
theorem facialDistance_attained [FiniteDimensional ℝ E] {V : Finset E}
    (hprop : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V) :
    ∃ Ψ : StrongDual ℝ E, exposedFace V Ψ ≠ V ∧
      ∃ y ∈ convexHull ℝ (↑(exposedFace V Ψ) : Set E),
        ∃ x ∈ convexHull ℝ (↑(V \ exposedFace V Ψ) : Set E),
          ‖y - x‖ = facialDistance V ∧ 0 < facialDistance V := by
  obtain ⟨ψ0, hψ0⟩ := hprop
  have hV : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hψ0 (by rw [h]; exact Finset.subset_empty.mp (h ▸ exposedFace_subset _ ψ0))
  -- for each proper face, a closest pair
  have hpair : ∀ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V →
      ∃ pq : E × E, pq.1 ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E) ∧
        pq.2 ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E) ∧
        ∀ p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E),
          ∀ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), ‖pq.1 - pq.2‖ ≤ ‖p - q‖ := by
    intro ψ hψ
    have hK : IsCompact (convexHull ℝ (↑(exposedFace V ψ) : Set E) ×ˢ
        convexHull ℝ (↑(V \ exposedFace V ψ) : Set E)) :=
      ((exposedFace V ψ).finite_toSet.isCompact_convexHull (𝕜 := ℝ)).prod
        ((V \ exposedFace V ψ).finite_toSet.isCompact_convexHull (𝕜 := ℝ))
    have hne1 := exposedFace_nonempty hV ψ
    have hne2 : (V \ exposedFace V ψ).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun h => hψ (Finset.Subset.antisymm (exposedFace_subset V ψ) h)
    obtain ⟨a, ha⟩ := hne1
    obtain ⟨b, hb⟩ := hne2
    obtain ⟨pq, hpq, hmin⟩ := hK.exists_isMinOn
      ⟨(a, b), subset_convexHull ℝ _ (by exact_mod_cast ha),
        subset_convexHull ℝ _ (by exact_mod_cast hb)⟩
      (continuous_norm.comp (continuous_fst.sub continuous_snd)).continuousOn
    exact ⟨pq, hpq.1, hpq.2, fun p hp q hq => by
      simpa using hmin (show (p, q) ∈ _ ×ˢ _ from ⟨hp, hq⟩)⟩
  -- the faces form a finite family; pick the one with the smallest closest-pair distance
  set fam := V.powerset.filter (fun F => ∃ ψ : StrongDual ℝ E, exposedFace V ψ = F ∧ F ≠ V)
    with hfam
  have hfamne : fam.Nonempty :=
    ⟨exposedFace V ψ0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (exposedFace_subset V ψ0),
      ψ0, rfl, hψ0⟩⟩
  have hchoose : ∀ F ∈ fam, ∃ ψ : StrongDual ℝ E, exposedFace V ψ = F ∧ F ≠ V :=
    fun F hF => (Finset.mem_filter.mp hF).2
  choose! ψF hψF using hchoose
  choose! PQ hPQ using fun F (hF : F ∈ fam) =>
    hpair (ψF F) (by rw [(hψF F hF).1]; exact (hψF F hF).2)
  obtain ⟨F, hF, hFmin⟩ := fam.exists_min_image (fun F => ‖(PQ F).1 - (PQ F).2‖) hfamne
  obtain ⟨hPQ1, hPQ2, hPQmin⟩ := hPQ F hF
  set Ψ := ψF F with hΨ
  have hΨF : exposedFace V Ψ = F := (hψF F hF).1
  have hΨne : exposedFace V Ψ ≠ V := hΨF ▸ (hψF F hF).2
  have hbdd : BddBelow {r : ℝ | ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V ∧
      ∃ p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E),
        ∃ q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E), r = ‖p - q‖} :=
    ⟨0, fun r ⟨_, _, _, _, _, _, hr⟩ => hr ▸ norm_nonneg _⟩
  have heq : facialDistance V = ‖(PQ F).1 - (PQ F).2‖ := by
    unfold facialDistance
    refine le_antisymm (csInf_le hbdd ⟨Ψ, hΨne, _, hPQ1, _, hPQ2, rfl⟩) ?_
    refine le_csInf ⟨_, Ψ, hΨne, _, hPQ1, _, hPQ2, rfl⟩ ?_
    rintro r ⟨ψ, hψ, p, hp, q, hq, rfl⟩
    have hG : exposedFace V ψ ∈ fam := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (exposedFace_subset V ψ), ψ, rfl, hψ⟩
    obtain ⟨hG1, hG2, hGmin⟩ := hPQ _ hG
    have hψG : exposedFace V (ψF (exposedFace V ψ)) = exposedFace V ψ := (hψF _ hG).1
    have h1 := hFmin _ hG
    have h2 := hGmin p (by rw [hψG]; exact hp) q (by rw [hψG]; exact hq)
    exact h1.trans h2
  refine ⟨Ψ, hΨne, (PQ F).1, hPQ1, (PQ F).2, hPQ2, heq.symm, ?_⟩
  rw [heq]
  refine norm_pos_iff.mpr (sub_ne_zero.mpr fun hpq => ?_)
  -- `Ψ` is maximal on `conv F` and strictly smaller on `conv (V \ F)`
  obtain ⟨wmax, hwV, hwmax⟩ := V.exists_max_image Ψ hV
  have hp := (mem_convexHull_exposedFace_iff Ψ
    (convexHull_mono (by exact_mod_cast exposedFace_subset V Ψ) hPQ1)).mp hPQ1
  have hlt : ∀ w ∈ V \ exposedFace V Ψ, Ψ w < Ψ wmax := by
    intro w hw
    obtain ⟨hwV', hwF⟩ := Finset.mem_sdiff.mp hw
    by_contra hge
    push Not at hge
    apply hwF
    unfold exposedFace
    exact Finset.mem_filter.mpr ⟨hwV', fun u hu => (hwmax u hu).trans hge⟩
  have hne3 : (V \ exposedFace V Ψ).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h => hΨne (Finset.Subset.antisymm (exposedFace_subset V Ψ) h)
  obtain ⟨w2, hw2, hw2max⟩ := (V \ exposedFace V Ψ).exists_max_image Ψ hne3
  have hq : Ψ (PQ F).2 ≤ Ψ w2 := apply_le_of_mem_convexHull Ψ hw2max hPQ2
  have h3 := hp wmax hwV
  rw [hpq] at h3
  linarith [hlt w2 hw2]

/-- **Proposition 2.31** (pyramidal width as facial distance). -/
theorem pyramidalWidth_eq_facialDistance [FiniteDimensional ℝ E] (V : Finset E) :
    pyramidalWidth V = facialDistance V := by
  classical
  by_cases hprop : ∃ ψ : StrongDual ℝ E, exposedFace V ψ ≠ V
  · obtain ⟨Ψ0, hΨ0, y, hyF0, x, hxF0, hdist, hδpos⟩ := facialDistance_attained hprop
    set δ := facialDistance V with hδ
    have hyV : y ∈ convexHull ℝ (↑V : Set E) :=
      convexHull_mono (by exact_mod_cast exposedFace_subset V Ψ0) hyF0
    have hΨ0y := (mem_convexHull_exposedFace_iff Ψ0 hyV).mp hyF0
    have hFsub : minFace V y ⊆ exposedFace V Ψ0 := by
      intro w hw
      unfold minFace at hw
      unfold exposedFace
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2 Ψ0 hΨ0y⟩
    obtain ⟨Ψ, hΨ, hface⟩ := minFace_exposed hyV
    have hyF : y ∈ convexHull ℝ (↑(minFace V y) : Set E) := mem_convexHull_minFace hyV
    have hxF : x ∈ convexHull ℝ (↑(V \ minFace V y) : Set E) :=
      convexHull_mono (by exact_mod_cast Finset.sdiff_subset_sdiff (le_refl V) hFsub) hxF0
    have hFne : exposedFace V Ψ ≠ V := by
      intro h
      apply hΨ0
      refine Finset.Subset.antisymm (exposedFace_subset V Ψ0) ?_
      intro w hw
      apply hFsub
      rw [hface, h]
      exact hw
    have hfar : ∀ a ∈ convexHull ℝ (↑(minFace V y) : Set E),
        ∀ b ∈ convexHull ℝ (↑(V \ minFace V y) : Set E), δ ≤ ‖a - b‖ := by
      intro a ha b hb
      rw [hface] at ha hb
      exact facialDistance_le hFne ha hb
    obtain ⟨f, hf0, hsep⟩ := separate_neighbourhood (convex_convexHull ℝ _) (convex_convexHull ℝ _)
      ⟨y, hyF⟩ ⟨x, hxF⟩ hδpos hfar
    have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    have hxy1 := hsep y hyF x hxF
    have hxy2 : f x - f y ≤ ‖f‖ * δ := by
      have := (f.le_opNorm (x - y))
      rw [map_sub] at this
      rw [norm_sub_rev x y, hdist] at this
      exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact this)
    have hfxy : f x - f y = ‖f‖ * δ := by linarith
    -- `f` is maximized at `y` over the minimal face, hence constant there
    have hmax : ∀ w ∈ minFace V y, f w ≤ f y := by
      intro w hw
      have := hsep w (subset_convexHull ℝ _ (by exact_mod_cast hw)) x hxF
      linarith
    have hconst := eq_of_mem_minFace_of_max hyV f hmax
    -- the support of `x` on its face of minimal `f`
    have hge : ∀ w ∈ V \ minFace V y, f x ≤ f w := by
      intro w hw
      have := hsep y hyF w (subset_convexHull ℝ _ (by exact_mod_cast hw))
      linarith
    set S := (V \ minFace V y).filter (fun w => f w = f x) with hS
    have hxS : x ∈ convexHull ℝ (↑S : Set E) := mem_convexHull_filter f hxF hge
    have hSV : S ⊆ V := (Finset.filter_subset _ _).trans Finset.sdiff_subset
    obtain ⟨a, ha⟩ : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.coe_empty, convexHull_empty] at hxS
      exact hxS
    have hfa : f a = f x := (Finset.mem_filter.mp ha).2
    have haS : ∀ w ∈ S, f w ≤ f a := fun w hw => by rw [(Finset.mem_filter.mp hw).2, hfa]
    obtain ⟨v, hv⟩ : (minFace V y).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.coe_empty, convexHull_empty] at hyF
      exact hyF
    have hvV : v ∈ V := (Finset.mem_filter.mp (show v ∈ minFace V y from hv)).1
    have hfv : f v = f y := hconst v hv
    have hvmin : ∀ w ∈ V, f v ≤ f w := by
      intro w hw
      by_cases hwF : w ∈ minFace V y
      · rw [hfv, hconst w hwF]
      · have := hge w (Finset.mem_sdiff.mpr ⟨hw, hwF⟩)
        have hk : 0 ≤ ‖f‖ * δ := mul_nonneg (norm_nonneg f) hδpos.le
        rw [hfv]
        linarith
    -- every scaling constant is at most `δ`
    have hupper : ∀ δ' ∈ {δ' : ℝ | 0 ≤ δ' ∧ IsScaling V δ'}, δ' ≤ δ := by
      rintro δ' ⟨hδ'0, hsc⟩
      have h1 := hsc S hSV x hxS y hyV f a ha haS v hvV hvmin
      have e1 : f (x - y) = ‖f‖ * δ := by rw [map_sub]; exact hfxy
      have e2 : f (a - v) = ‖f‖ * δ := by rw [map_sub, hfa, hfv]; exact hfxy
      have e3 : ‖x - y‖ = δ := by rw [norm_sub_rev]; exact hdist
      rw [e1, e2, e3] at h1
      have hk : 0 < ‖f‖ * δ := mul_pos hfpos hδpos
      exact le_of_mul_le_mul_right (by linarith [h1, mul_comm (‖f‖ * δ) δ]) hk
    have hne : ({δ' : ℝ | 0 ≤ δ' ∧ IsScaling V δ'}).Nonempty := ⟨0, le_rfl, isScaling_zero V⟩
    have hbdd : BddAbove {δ' : ℝ | 0 ≤ δ' ∧ IsScaling V δ'} := ⟨δ, hupper⟩
    unfold pyramidalWidth
    refine le_antisymm (csSup_le hne hupper) ?_
    exact le_csSup hbdd ⟨hδpos.le, facialDistance_isScaling V⟩
  · push Not at hprop
    -- no proper face: `V` has at most one point
    have hsub : (↑V : Set E).Subsingleton := by
      intro p hp q hq
      by_contra hpq
      obtain ⟨g, hg⟩ := geometric_hahn_banach_point_point (Ne.symm hpq)
      have hq' : q ∈ exposedFace V g := by rw [hprop g]; exact hq
      unfold exposedFace at hq'
      have := (Finset.mem_filter.mp hq').2 p hp
      linarith
    have hfd : facialDistance V = 0 := by
      unfold facialDistance
      convert Real.sInf_empty
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ψ, hψ, -⟩
      exact hψ (hprop ψ)
    have hall : ∀ δ' : ℝ, IsScaling V δ' := by
      intro δ' S hS x hx y hy ψ a ha haS v hv hvV
      have hx' : x ∈ convexHull ℝ (↑V : Set E) := convexHull_mono (by exact_mod_cast hS) hx
      have hxy : x = y := by
        rcases hsub.eq_empty_or_singleton with h | ⟨p, hp⟩
        · rw [h, convexHull_empty] at hy
          exact absurd hy (Set.notMem_empty _)
        · rw [hp, convexHull_singleton] at hx' hy
          exact (Set.mem_singleton_iff.mp hx').trans (Set.mem_singleton_iff.mp hy).symm
      rw [hxy, sub_self, map_zero, mul_zero, norm_zero, mul_zero]
    have hnb : ¬ BddAbove {δ' : ℝ | 0 ≤ δ' ∧ IsScaling V δ'} := by
      rintro ⟨M, hM⟩
      have h0 : (0 : ℝ) ≤ max M 0 + 1 := by linarith [le_max_right M 0]
      have h := hM (show max M 0 + 1 ∈ {δ' : ℝ | 0 ≤ δ' ∧ IsScaling V δ'} from ⟨h0, hall _⟩)
      linarith [le_max_left M 0]
    unfold pyramidalWidth
    rw [hfd, Real.sSup_of_not_bddAbove hnb]

end Proof

end Lemmata.AwayStepFW
