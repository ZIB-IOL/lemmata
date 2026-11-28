module

public import Lemmata.FWProduct.Relint

@[expose] public section

/-!
# Products of `k` polytopes (Corollary A.3)

The facial distance is invariant under linear isometries. The Euclidean product of `k + 1` copies
of `E` is isometric to the Euclidean product of `E` with the product of `k` copies, so the exact
two-factor formula of Theorem 4.5 gives the pyramidal width of a product of `k` polytopes by
induction: `δ⁻² = ∑ δᵢ⁻²`.
-/

namespace Lemmata.FWProduct

open Lemmata.FrankWolfe Lemmata.AwayStepFW

universe u

section Iso

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A functional pulled back along a linear isometry. -/
noncomputable def compIso (ψ : StrongDual ℝ F) (e : E ≃ₗᵢ[ℝ] F) : StrongDual ℝ E :=
  ψ.comp e.toContinuousLinearEquiv.toContinuousLinearMap

theorem compIso_apply (ψ : StrongDual ℝ F) (e : E ≃ₗᵢ[ℝ] F) (v : E) :
    compIso ψ e v = ψ (e v) := rfl

open Classical in
theorem exposedFace_image (e : E ≃ₗᵢ[ℝ] F) (V : Finset E) (ψ : StrongDual ℝ F) :
    exposedFace (V.image e) ψ = (exposedFace V (compIso ψ e)).image e := by
  classical
  ext w
  unfold exposedFace
  constructor
  · intro h
    obtain ⟨hw, hmax⟩ := Finset.mem_filter.mp h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, fun u hu => ?_⟩, rfl⟩
    rw [compIso_apply, compIso_apply]
    exact hmax (e u) (Finset.mem_image_of_mem e hu)
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hv, hmax⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem e hv, fun u hu => ?_⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    have := hmax u' hu'
    rwa [compIso_apply, compIso_apply] at this

theorem image_convexHull_iso (e : E ≃ₗᵢ[ℝ] F) (s : Set E) :
    convexHull ℝ (e '' s) = e '' convexHull ℝ s :=
  (e.toLinearEquiv.toLinearMap.image_convexHull s).symm

open Classical in
theorem facialDistance_image_cl (e : E ≃ₗᵢ[ℝ] F) (V : Finset E) :
    facialDistance (V.image e) = facialDistance V := by
  classical
  have hinj : Function.Injective e := e.injective
  have hsd : ∀ G : Finset E, V.image e \ G.image e = (V \ G).image e := fun G =>
    (Finset.image_sdiff V G hinj).symm
  have hcomp : ∀ φ : StrongDual ℝ E, compIso (compIso φ e.symm) e = φ := fun φ => by
    ext v; simp [compIso_apply]
  unfold facialDistance
  congr 1
  ext r
  constructor
  · rintro ⟨ψ, hψ, p, hp, q, hq, rfl⟩
    rw [exposedFace_image] at hψ hp hq
    rw [hsd, Finset.coe_image, image_convexHull_iso] at hq
    rw [Finset.coe_image, image_convexHull_iso] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    refine ⟨compIso ψ e, fun h => hψ (by rw [h]), p', hp', q', hq', ?_⟩
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  · rintro ⟨φ, hφ, p, hp, q, hq, rfl⟩
    refine ⟨compIso φ e.symm, ?_, e p, ?_, e q, ?_, ?_⟩
    · rw [exposedFace_image, hcomp]
      intro h
      apply hφ
      have := congrArg (Finset.image e.symm) h
      simpa [Finset.image_image] using this
    · rw [exposedFace_image, hcomp, Finset.coe_image, image_convexHull_iso]
      exact ⟨p, hp, rfl⟩
    · rw [exposedFace_image, hcomp, hsd, Finset.coe_image, image_convexHull_iso]
      exact ⟨q, hq, rfl⟩
    · rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- The facial distance is invariant under linear isometries (for any decidable equality used to
form the image). -/
theorem facialDistance_image {inst : DecidableEq F} (e : E ≃ₗᵢ[ℝ] F) (V : Finset E) :
    facialDistance (@Finset.image E F inst e V) = facialDistance V := by
  classical
  convert facialDistance_image_cl e V using 2
  ext x
  simp only [Finset.mem_image]

end Iso

section Pi

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean product of one copy of `E` is `E`. -/
noncomputable def uniqueIso : PiLp 2 (fun _ : Fin 1 => E) ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (Fin 1 → E)).trans (LinearEquiv.funUnique (Fin 1) ℝ E)
  norm_map' x := by
    have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 => E) x
    rw [Fin.sum_univ_one] at h1
    have h2 : ‖x 0‖ = ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), h1]
    exact h2

/-- The Euclidean product of `k + 1` copies of `E` is the Euclidean product of `E` with the
product of `k` copies. -/
noncomputable def consIso (k : ℕ) :
    WithLp 2 (E × PiLp 2 (fun _ : Fin k => E)) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin (k + 1) => E) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (E × PiLp 2 (fun _ : Fin k => E))).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl ℝ E) (WithLp.linearEquiv 2 ℝ (Fin k → E))).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (k + 1) => E)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (k + 1) → E)).symm))
  norm_map' x := by
    show ‖WithLp.toLp 2 (Fin.cons x.fst (WithLp.ofLp x.snd) : Fin (k + 1) → E)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ,
      WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp

end Pi

section Many

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem mem_piVertices {k : ℕ} {V : Fin k → Finset E} {x : PiLp 2 (fun _ : Fin k => E)} :
    x ∈ piVertices V ↔ ∀ i, x i ∈ V i := by
  classical
  unfold piVertices
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    exact Fintype.mem_piFinset.mp hf i
  · intro h
    exact ⟨WithLp.ofLp x, Fintype.mem_piFinset.mpr h, rfl⟩

open Classical in
theorem piVertices_one (V : Fin 1 → Finset E) :
    piVertices V = (V 0).image (uniqueIso E).symm := by
  classical
  ext x
  rw [mem_piVertices, Finset.mem_image]
  constructor
  · intro h
    exact ⟨uniqueIso E x, h 0, (uniqueIso E).symm_apply_apply x⟩
  · rintro ⟨v, hv, rfl⟩ i
    rw [Fin.fin_one_eq_zero i]
    exact hv

theorem consIso_zero (k : ℕ) (y : WithLp 2 (E × PiLp 2 (fun _ : Fin k => E))) :
    consIso E k y 0 = y.fst := rfl

theorem consIso_succ (k : ℕ) (y : WithLp 2 (E × PiLp 2 (fun _ : Fin k => E))) (i : Fin k) :
    consIso E k y i.succ = y.snd i := rfl

open Classical in
theorem piVertices_succ {k : ℕ} (V : Fin (k + 1) → Finset E) :
    piVertices V =
      (productVertices (V 0) (piVertices (fun i => V i.succ))).image (consIso E k) := by
  classical
  ext x
  rw [mem_piVertices, Finset.mem_image]
  constructor
  · intro h
    refine ⟨(consIso E k).symm x, ?_, (consIso E k).apply_symm_apply x⟩
    rw [mem_productVertices]
    refine ⟨((consIso E k).symm x).fst, ?_, ((consIso E k).symm x).snd, ?_, rfl⟩
    · have := h 0
      rwa [← (consIso E k).apply_symm_apply x, consIso_zero] at this
    · rw [mem_piVertices]
      intro i
      have := h i.succ
      rwa [← (consIso E k).apply_symm_apply x, consIso_succ] at this
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_productVertices.mp hy
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [consIso_zero]; exact ha
    · rw [consIso_succ]; exact (mem_piVertices.mp hb) j

omit [InnerProductSpace ℝ E] in
theorem card_piVertices {k : ℕ} (V : Fin k → Finset E) :
    (piVertices V).card = ∏ i, (V i).card := by
  classical
  unfold piVertices
  rw [Finset.card_image_of_injective _ (WithLp.toLp_injective 2), Fintype.card_piFinset]

omit [InnerProductSpace ℝ E] in
theorem one_lt_card_piVertices {k : ℕ} {V : Fin (k + 1) → Finset E}
    (hV : ∀ i, 1 < (V i).card) : 1 < (piVertices V).card := by
  rw [card_piVertices]
  have hpos : 0 < ∏ i, (V i).card := Finset.prod_pos (fun i _ => by have := hV i; omega)
  calc 1 < (V 0).card := hV 0
    _ ≤ ∏ i, (V i).card :=
        Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem (fun i => (V i).card) (Finset.mem_univ 0))

open Classical in
/-- A finite set with at least two points has positive facial distance. -/
theorem facialDistance_pos {V : Finset E} (hV : 1 < V.card) : 0 < facialDistance V := by
  classical
  obtain ⟨ψ, hψ, p, hp, q, hq, heq⟩ := facialDistance_attained (exists_proper_face hV)
  rw [← heq]
  have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨f₀, hf₀⟩ := Proof.exposedFace_nonempty hVne ψ
  have hfF : ∀ w ∈ exposedFace V ψ, w ∈ V ∧ ∀ u ∈ V, ψ u ≤ ψ w := fun w hw => by
    unfold exposedFace at hw
    exact Finset.mem_filter.mp hw
  have hψp : ψ p = ψ f₀ := apply_eq_of_mem_affineSpan ψ (fun w hw => le_antisymm
    ((hfF f₀ hf₀).2 w (hfF w (Finset.mem_coe.mp hw)).1)
    ((hfF w (Finset.mem_coe.mp hw)).2 f₀ (hfF f₀ hf₀).1)) (convexHull_subset_affineSpan _ hp)
  obtain ⟨u, hu⟩ := sdiff_exposedFace_nonempty hψ
  obtain ⟨w₀, hw₀, hmax⟩ := (V \ exposedFace V ψ).exists_max_image ψ ⟨u, hu⟩
  have hlt : ψ w₀ < ψ f₀ := by
    rw [Finset.mem_sdiff] at hw₀
    by_contra hle
    apply hw₀.2
    unfold exposedFace
    exact Finset.mem_filter.mpr ⟨hw₀.1, fun v hv => ((hfF f₀ hf₀).2 v hv).trans (not_lt.mp hle)⟩
  have hψq : ψ q ≤ ψ w₀ := le_on_hull ψ hmax q hq
  have hne : p ≠ q := fun h => by rw [h] at hψp; linarith
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)

/-- The two-factor formula in reciprocal form. -/
theorem formula_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2)) =
      (a ^ (-2 : ℝ) + b ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  have e : a ^ (-2 : ℝ) + b ^ (-2 : ℝ) = (a ^ 2 * b ^ 2 / (a ^ 2 + b ^ 2))⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, Real.rpow_two, Real.rpow_two]
    field_simp
    ring
  rw [e, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
    Real.sqrt_eq_rpow]

variable [FiniteDimensional ℝ E]

/-- **Corollary A.3**, the exact value. -/
theorem product_width_many_eq :
    ∀ (k : ℕ) (V : Fin (k + 1) → Finset E), (∀ i, 1 < (V i).card) →
      facialDistance (piVertices V) = (∑ i, facialDistance (V i) ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro V hV
    rw [piVertices_one, facialDistance_image, Fin.sum_univ_one,
      ← Real.rpow_mul (facialDistance_pos (hV 0)).le]
    norm_num
  | succ k ih =>
    intro V hV
    have hW : ∀ i : Fin (k + 1), 1 < (V i.succ).card := fun i => hV i.succ
    have hih : facialDistance (piVertices (fun i : Fin (k + 1) => V i.succ)) =
        (∑ i : Fin (k + 1), facialDistance (V i.succ) ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) := ih _ hW
    rw [piVertices_succ, facialDistance_image,
      pyramidal_width_product (hV 0) (one_lt_card_piVertices hW), hih,
      Fin.sum_univ_succ (f := fun i => facialDistance (V i) ^ (-2 : ℝ))]
    have ha := facialDistance_pos (hV 0)
    have hSpos : 0 < ∑ i : Fin (k + 1), facialDistance (V i.succ) ^ (-2 : ℝ) :=
      Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (facialDistance_pos (hV i.succ)) _)
        Finset.univ_nonempty
    rw [formula_inv ha (Real.rpow_pos_of_pos hSpos _), ← Real.rpow_mul hSpos.le]
    norm_num

/-- **Corollary A.3**, the lower bound. -/
theorem product_width_many_bound {k : ℕ} {V : Fin (k + 1) → Finset E}
    (hV : ∀ i, 1 < (V i).card) {m : ℝ} (hm : 0 ≤ m) (hmV : ∀ i, m ≤ facialDistance (V i)) :
    m / Real.sqrt (k + 1) ≤ facialDistance (piVertices V) := by
  rw [product_width_many_eq k V hV]
  rcases eq_or_lt_of_le hm with h0 | hmpos
  · rw [← h0, zero_div]; exact Real.rpow_nonneg (Finset.sum_nonneg (fun i _ =>
      Real.rpow_nonneg (facialDistance_pos (hV i)).le _)) _
  have hS : ∑ i, facialDistance (V i) ^ (-2 : ℝ) ≤ (k + 1) * m ^ (-2 : ℝ) := by
    calc ∑ i, facialDistance (V i) ^ (-2 : ℝ) ≤ ∑ _i : Fin (k + 1), m ^ (-2 : ℝ) :=
          Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow_of_nonpos hmpos (hmV i) (by norm_num))
      _ = (k + 1) * m ^ (-2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hSpos : 0 < ∑ i, facialDistance (V i) ^ (-2 : ℝ) :=
    Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (facialDistance_pos (hV i)) _)
      Finset.univ_nonempty
  calc m / Real.sqrt (k + 1) = ((k + 1) * m ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hmpos.le,
          Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
        norm_num
        rw [div_eq_mul_inv, mul_comm]
    _ ≤ (∑ i, facialDistance (V i) ^ (-2 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hSpos hS (by norm_num)

end Many

namespace Proof

theorem product_width_many : ProductWidthMany.{u} := by
  intro E _ _ _ k V hV
  exact ⟨product_width_many_eq k V hV, fun m hm hmV => product_width_many_bound hV hm hmV⟩

end Proof

end Lemmata.FWProduct
