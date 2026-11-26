module

public import Lemmata.AwayStepFW.Defs
public import Lemmata.FrankWolfe.Polytope.Faces

@[expose] public section

/-!
# Facial distance (Proposition 2.31, lower bound)

The facial distance of `conv V` is the smallest distance between a proper exposed face and the
convex hull of the remaining vertices. It is a scaling constant, so the pyramidal width is at least
the facial distance.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Proof

theorem facialDistance_nonneg (V : Finset E) : 0 ≤ facialDistance V := by
  unfold facialDistance
  exact Real.sInf_nonneg (fun r ⟨_, _, _, _, _, _, hr⟩ => hr ▸ norm_nonneg _)

open Classical in
theorem facialDistance_le {V : Finset E} {ψ : StrongDual ℝ E} (hF : exposedFace V ψ ≠ V) {p q : E}
    (hp : p ∈ convexHull ℝ (↑(exposedFace V ψ) : Set E))
    (hq : q ∈ convexHull ℝ (↑(V \ exposedFace V ψ) : Set E)) : facialDistance V ≤ ‖p - q‖ := by
  classical
  unfold facialDistance
  exact csInf_le ⟨0, fun r ⟨_, _, _, _, _, _, hr⟩ => hr ▸ norm_nonneg _⟩ ⟨ψ, hF, p, hp, q, hq, rfl⟩

/-- Pushing away from a vertex does not enlarge the minimal face. -/
theorem minFace_push_subset {V : Finset E} {y v : E} (hv : v ∈ V) {γ : ℝ} (hγ : 0 ≤ γ) :
    minFace V ((1 + γ) • y - γ • v) ⊆ minFace V y := by
  classical
  intro w hw
  simp only [minFace, Finset.mem_filter] at hw ⊢
  refine ⟨hw.1, fun ψ hψ => hw.2 ψ (fun u hu => ?_)⟩
  have h1 := hψ u hu
  have h2 := hψ v hv
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  nlinarith

/-- The base case: if the minimal face of `y` contains no vertex of `S`, the scaling inequality
holds with the facial distance. -/
theorem scaling_base {V S : Finset E} (hS : S ⊆ V) {x y : E} (hx : x ∈ convexHull ℝ (↑S : Set E))
    (hy : y ∈ convexHull ℝ (↑V : Set E)) (hdisj : ∀ w ∈ S, w ∉ minFace V y) (ψ : StrongDual ℝ E)
    {a v : E} (ha : a ∈ S) (haS : ∀ w ∈ S, ψ w ≤ ψ a) (_hv : v ∈ V) (hvV : ∀ w ∈ V, ψ v ≤ ψ w) :
    facialDistance V * ψ (x - y) ≤ ψ (a - v) * ‖x - y‖ := by
  classical
  obtain ⟨Ψ, hΨ, hface⟩ := minFace_exposed hy
  have hyF : y ∈ convexHull ℝ (↑(exposedFace V Ψ) : Set E) := hface ▸ mem_convexHull_minFace hy
  have hSsub : S ⊆ V \ exposedFace V Ψ := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨hS hw, fun h => hdisj w hw (hface ▸ h)⟩
  have hxF : x ∈ convexHull ℝ (↑(V \ exposedFace V Ψ) : Set E) :=
    convexHull_mono (by exact_mod_cast hSsub) hx
  have hFV : exposedFace V Ψ ≠ V := by
    intro h
    have := hSsub ha
    rw [h, Finset.sdiff_self] at this
    exact (Finset.notMem_empty a) this
  have hfd := facialDistance_le hFV hyF hxF
  rw [norm_sub_rev] at hfd
  have hxa : ψ x ≤ ψ a := apply_le_of_mem_convexHull ψ haS hx
  have hvy : ψ v ≤ ψ y := by
    have hsub : (↑V : Set E) ⊆ {z | ψ v ≤ ψ z} := fun w hw => hvV w hw
    exact convexHull_min hsub (convex_halfSpace_ge ψ.toLinearMap.isLinear _) hy
  have hva : ψ v ≤ ψ a := hvV a (hS ha)
  have h0 := facialDistance_nonneg V
  rw [map_sub, map_sub]
  rcases le_or_gt (ψ x - ψ y) 0 with hneg | hpos
  · nlinarith [norm_nonneg (x - y), mul_nonpos_of_nonneg_of_nonpos h0 hneg]
  · nlinarith [mul_le_mul_of_nonneg_left hfd hpos.le, norm_nonneg (x - y)]

open Classical in
/-- Pushing `x ∈ conv S` away from `v ∈ S` along a representation with weight `c v < 1` on `v`. -/
theorem x_push {S : Finset E} {v : E} (hvS : v ∈ S) {c : E → ℝ} (hc0 : ∀ w ∈ S, 0 ≤ c w)
    (hc1 : ∑ w ∈ S, c w = 1) {x : E} (hcx : ∑ w ∈ S, c w • w = x) (hcv : c v < 1) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ c v / (1 - c v)) :
    (1 + γ) • x - γ • v ∈ convexHull ℝ (↑S : Set E) ∧
      (γ = c v / (1 - c v) → (1 + γ) • x - γ • v ∈ convexHull ℝ (↑(S.erase v) : Set E)) := by
  classical
  set c' : E → ℝ := fun w => (1 + γ) * c w - if w = v then γ else 0 with hc'
  have hnn : ∀ w ∈ S, 0 ≤ c' w := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      have : γ * (1 - c w) ≤ c w := by rw [← le_div_iff₀ (by linarith)]; exact hγ
      simp only [hc', ite_true]; nlinarith
    · simp only [hc', hwv, ite_false, sub_zero]; exact mul_nonneg (by linarith) (hc0 w hw)
  have hsum : ∑ w ∈ S, c' w = 1 := by
    simp only [hc', Finset.sum_sub_distrib, ← Finset.mul_sum, hc1, Finset.sum_ite_eq', hvS,
      ite_true]
    ring
  have hrep : ∑ w ∈ S, c' w • w = (1 + γ) • x - γ • v := by
    simp only [hc', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hcx, ite_smul,
      zero_smul, Finset.sum_ite_eq', hvS, ite_true]
  refine ⟨Finset.mem_convexHull'.mpr ⟨c', hnn, hsum, hrep⟩, fun hγeq => ?_⟩
  have hzero : c' v = 0 := by
    simp only [hc', ite_true, hγeq]; field_simp; ring
  refine Finset.mem_convexHull'.mpr ⟨c', fun w hw => hnn w (Finset.mem_of_mem_erase hw), ?_, ?_⟩
  · rw [Finset.sum_erase _ hzero]; exact hsum
  · rw [Finset.sum_erase _ (by rw [hzero, zero_smul])]; exact hrep

/-- The largest push of `y ∈ conv V` away from a vertex `v ≠ y` that stays in `conv V`. -/
theorem y_push [FiniteDimensional ℝ E] {V : Finset E} {y v : E} (hy : y ∈ convexHull ℝ (↑V : Set E))
    (hyv : y ≠ v) :
    ∃ γy : ℝ, 0 ≤ γy ∧ (∀ γ ∈ Set.Icc (0 : ℝ) γy, (1 + γ) • y - γ • v ∈ convexHull ℝ (↑V : Set E)) ∧
      v ∉ minFace V ((1 + γy) • y - γy • v) := by
  classical
  set K : Set ℝ := {γ | 0 ≤ γ ∧ (1 + γ) • y - γ • v ∈ convexHull ℝ (↑V : Set E)} with hK
  have hcpt : IsCompact (convexHull ℝ (↑V : Set E)) := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hcont : Continuous (fun γ : ℝ => (1 + γ) • y - γ • v) := by fun_prop
  have hclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_id).inter (hcpt.isClosed.preimage hcont)
  have hne : K.Nonempty := ⟨0, le_rfl, by simpa using hy⟩
  have hd : 0 < ‖y - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyv)
  have hbdd : BddAbove K := by
    refine ⟨Metric.diam (convexHull ℝ (↑V : Set E)) / ‖y - v‖, fun γ hγ => ?_⟩
    rw [le_div_iff₀ hd]
    have := Metric.dist_le_diam_of_mem hcpt.isBounded hγ.2 hy
    rw [dist_eq_norm, show (1 + γ) • y - γ • v - y = γ • (y - v) by module, norm_smul,
      Real.norm_of_nonneg hγ.1] at this
    exact this
  set γy := sSup K with hγy
  have hmem : γy ∈ K := hclosed.csSup_mem hne hbdd
  refine ⟨γy, hmem.1, fun γ hγ => ?_, fun hvF => ?_⟩
  · rcases eq_or_lt_of_le hγ.1 with h0 | hpos
    · rw [← h0]; simpa using hy
    · have hγy0 : 0 < γy := lt_of_lt_of_le hpos hγ.2
      have hcomb := (convex_convexHull ℝ (↑V : Set E)) hy hmem.2
        (sub_nonneg.mpr ((div_le_one hγy0).mpr hγ.2)) (div_nonneg hγ.1 hγy0.le) (by ring)
      convert hcomb using 1
      match_scalars <;> field_simp
      ring
  · obtain ⟨γ', hγ'0, hγ'⟩ := push_away hmem.2 hvF
    have hmem' : γy + γ' * (1 + γy) ∈ K := by
      refine ⟨by nlinarith [hmem.1], ?_⟩
      convert hγ' using 1
      module
    have := le_csSup hbdd hmem'
    nlinarith [hmem.1]

/-- **Proposition 2.31, lower bound.** The facial distance is a scaling constant of `conv V`. -/
theorem facialDistance_isScaling [FiniteDimensional ℝ E] (V : Finset E) :
    IsScaling V (facialDistance V) := by
  classical
  suffices H : ∀ n : ℕ, ∀ (S : Finset E) (x y : E), (minFace V y ∩ S).card = n → S ⊆ V →
      x ∈ convexHull ℝ (↑S : Set E) → y ∈ convexHull ℝ (↑V : Set E) →
      ∀ ψ : StrongDual ℝ E, ∀ a ∈ S, (∀ w ∈ S, ψ w ≤ ψ a) → ∀ vF ∈ V, (∀ w ∈ V, ψ vF ≤ ψ w) →
        facialDistance V * ψ (x - y) ≤ ψ (a - vF) * ‖x - y‖ by
    intro S hS x hx y hy ψ a ha haS v hv hvV
    exact H _ S x y rfl hS hx hy ψ a ha haS v hv hvV
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S x y hn hS hx hy ψ a ha haS vF hvF hvFV
  by_cases hdisj : ∀ w ∈ S, w ∉ minFace V y
  · exact scaling_base hS hx hy hdisj ψ ha haS hvF hvFV
  push Not at hdisj
  obtain ⟨v, hvS, hvM⟩ := hdisj
  have hvV : v ∈ V := hS hvS
  by_cases hxy : x = y
  · rw [hxy, sub_self, map_zero, mul_zero, norm_zero, mul_zero]
  have hvmem : v ∈ minFace V y ∩ S := Finset.mem_inter.mpr ⟨hvM, hvS⟩
  have finish : ∀ γ : ℝ, 0 ≤ γ → ∀ S' ⊆ S, (1 + γ) • x - γ • v ∈ convexHull ℝ (↑S' : Set E) →
      (1 + γ) • y - γ • v ∈ convexHull ℝ (↑V : Set E) →
      (minFace V ((1 + γ) • y - γ • v) ∩ S').card < n →
      facialDistance V * ψ (x - y) ≤ ψ (a - vF) * ‖x - y‖ := by
    intro γ hγ S' hS'S hx' hy' hcard
    have hS'ne : S'.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.coe_empty, convexHull_empty] at hx'
      exact hx'
    obtain ⟨a', ha', ha'S⟩ := S'.exists_max_image ψ hS'ne
    have hIH := ih _ hcard S' _ _ rfl (hS'S.trans hS) hx' hy' ψ a' ha' ha'S vF hvF hvFV
    have hdiff : ((1 + γ) • x - γ • v) - ((1 + γ) • y - γ • v) = (1 + γ) • (x - y) := by module
    rw [hdiff, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg (by linarith)] at hIH
    have hpos : 0 < 1 + γ := by linarith
    have h3 : (1 + γ) * (facialDistance V * ψ (x - y)) ≤ (1 + γ) * (ψ (a' - vF) * ‖x - y‖) := by
      linarith [hIH]
    have h2 := le_of_mul_le_mul_left h3 hpos
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [map_sub, map_sub]
    linarith [haS a' (hS'S ha')]
  have hmono : ∀ γ : ℝ, 0 ≤ γ → minFace V ((1 + γ) • y - γ • v) ⊆ minFace V y :=
    fun γ hγ => minFace_push_subset hvV hγ
  have hxblock : ∀ γ : ℝ, 0 ≤ γ → (minFace V ((1 + γ) • y - γ • v) ∩ S.erase v).card < n := by
    intro γ hγ
    rw [← hn]
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨v, hvmem, fun h => ?_⟩
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨hmono γ hγ hw1, Finset.mem_of_mem_erase hw2⟩
    · exact (Finset.notMem_erase v S) (Finset.mem_inter.mp h).2
  have hyblock : ∀ γ : ℝ, 0 ≤ γ → v ∉ minFace V ((1 + γ) • y - γ • v) →
      (minFace V ((1 + γ) • y - γ • v) ∩ S).card < n := by
    intro γ hγ hvnot
    rw [← hn]
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr
      ⟨v, hvmem, fun h => hvnot (Finset.mem_inter.mp h).1⟩
    intro w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨hmono γ hγ hw1, hw2⟩
  obtain ⟨c, hc0, hc1, hcx⟩ := Finset.mem_convexHull'.mp hx
  have hcv_le : c v ≤ 1 := hc1 ▸ Finset.single_le_sum (fun w hw => hc0 w hw) hvS
  rcases lt_or_eq_of_le hcv_le with hcv | hcv
  · set γx := c v / (1 - c v) with hγx
    have hγx0 : 0 ≤ γx := div_nonneg (hc0 v hvS) (by linarith)
    have hxe := (x_push hvS hc0 hc1 hcx hcv hγx0 le_rfl).2 rfl
    by_cases hyv : y = v
    · have hy' : (1 + γx) • y - γx • v ∈ convexHull ℝ (↑V : Set E) := by
        rw [hyv, add_smul, one_smul, add_sub_cancel_right]; rw [← hyv]; exact hy
      exact finish γx hγx0 (S.erase v) (Finset.erase_subset v S) hxe hy' (hxblock γx hγx0)
    · obtain ⟨γy, hγy0, hγyI, hvnot⟩ := y_push hy hyv
      rcases le_total γx γy with hle | hle
      · exact finish γx hγx0 (S.erase v) (Finset.erase_subset v S) hxe (hγyI γx ⟨hγx0, hle⟩)
          (hxblock γx hγx0)
      · exact finish γy hγy0 S le_rfl (x_push hvS hc0 hc1 hcx hcv hγy0 hle).1
          (hγyI γy ⟨hγy0, le_rfl⟩) (hyblock γy hγy0 hvnot)
  · have hxv : x = v := by
      have hzero : ∀ w ∈ S.erase v, c w = 0 := by
        have := Finset.sum_erase_add S c hvS
        rw [hc1, hcv] at this
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => hc0 w (Finset.mem_of_mem_erase hw))).mp
          (by linarith)
      rw [← hcx, ← Finset.sum_erase_add S _ hvS, hcv, one_smul,
        Finset.sum_eq_zero (fun w hw => by rw [hzero w hw, zero_smul]), zero_add]
    have hyv : y ≠ v := fun h => hxy (hxv.trans h.symm)
    obtain ⟨γy, hγy0, hγyI, hvnot⟩ := y_push hy hyv
    have hx' : (1 + γy) • x - γy • v ∈ convexHull ℝ (↑S : Set E) := by
      rw [hxv, add_smul, one_smul, add_sub_cancel_right]
      exact subset_convexHull ℝ _ (by exact_mod_cast hvS)
    exact finish γy hγy0 S le_rfl hx' (hγyI γy ⟨hγy0, le_rfl⟩) (hyblock γy hγy0 hvnot)

end Proof

end Lemmata.AwayStepFW
