module

public import Lemmata.AwayStepFW.Statement
public import Lemmata.FrankWolfe.Proof.Calculus
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Simplex-like polytopes: sparsity scaling and feasibility of DI-PFW

The decomposition of Garber and Hazan (Lemma 5.3) is obtained by minimizing the total weight that
has to be moved: among all ways to write `x = ∑ (γ_u - Δ_u) u + (∑ Δ) z` with `z ∈ P`, take one
with `∑ Δ` minimal. If some `u` with `Δ_u > 0` had its support inside that of `z`, a little weight
could be moved from `z` back to `u` without leaving `P = {x ≥ 0} ∩ W`.
-/

namespace Lemmata.AwayStepFW

open Lemmata.FrankWolfe

namespace Proof

variable {n : ℕ}

theorem hull_nonneg {V : Finset (EuclideanSpace ℝ (Fin n))}
    {W : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))}
    (hP : convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) = {x | ∀ i, 0 ≤ x i} ∩ (W : Set _))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))))
    (i : Fin n) : 0 ≤ x i := by
  rw [hP] at hx
  exact hx.1 i

theorem hull_mem_W {V : Finset (EuclideanSpace ℝ (Fin n))}
    {W : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))}
    (hP : convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) = {x | ∀ i, 0 ≤ x i} ∩ (W : Set _))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) :
    x ∈ W := by
  rw [hP] at hx
  exact hx.2

/-- In a nonnegative combination of nonnegative vectors, every vector with positive weight has its
support inside that of the combination. -/
theorem support_sub_of_sum {V : Finset (EuclideanSpace ℝ (Fin n))}
    (hV : ∀ v ∈ V, ∀ i, 0 ≤ v i) {lam : EuclideanSpace ℝ (Fin n) → ℝ}
    (hlam : ∀ w ∈ V, 0 ≤ lam w) {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ V) (hpos : 0 < lam w)
    (i : Fin n) (hi : (∑ u ∈ V, lam u • u) i = 0) : w i = 0 := by
  have hi' : ∑ u ∈ V, lam u * u i = 0 := by simpa using hi
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u hu => mul_nonneg (hlam u hu) (hV u hu i))).mp hi' w hw
  rcases mul_eq_zero.mp hterm with h | h
  · linarith
  · exact h

/-- A point of `conv V` whose support lies in that of `x` is below every maximizer of `ψ` over the
vertices whose support lies in that of `x`. -/
theorem le_of_support {V : Finset (EuclideanSpace ℝ (Fin n))} (hV : ∀ v ∈ V, ∀ i, 0 ≤ v i)
    (ψ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) {x a z : EuclideanSpace ℝ (Fin n)}
    (ha : ∀ w ∈ V, (∀ i, x i = 0 → w i = 0) → ψ w ≤ ψ a)
    (hz : z ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))))
    (hzx : ∀ i, x i = 0 → z i = 0) : ψ z ≤ ψ a := by
  obtain ⟨lam, hlam0, hlam1, hzeq⟩ := Finset.mem_convexHull'.mp hz
  rw [← hzeq, map_sum]
  calc ∑ w ∈ V, ψ (lam w • w) ≤ ∑ w ∈ V, lam w * ψ a := by
        apply Finset.sum_le_sum
        intro w hw
        rw [map_smul, smul_eq_mul]
        rcases eq_or_lt_of_le (hlam0 w hw) with h0 | hpos
        · rw [← h0]
          simp
        · apply mul_le_mul_of_nonneg_left _ hpos.le
          apply ha w hw
          intro i hi
          exact support_sub_of_sum hV hlam0 hw hpos i (by rw [hzeq]; exact hzx i hi)
    _ = ψ a := by rw [← Finset.sum_mul, hlam1, one_mul]

/-- The decomposition of Garber and Hazan (Lemma 5.3) for simplex-like polytopes. -/
theorem gh_decomposition {V : Finset (EuclideanSpace ℝ (Fin n))}
    {W : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))}
    (hP : convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) = {x | ∀ i, 0 ≤ x i} ∩ (W : Set _))
    (h01 : ∀ v ∈ V, ∀ i, v i = 0 ∨ v i = 1)
    {γ : EuclideanSpace ℝ (Fin n) → ℝ} (hγ0 : ∀ u ∈ V, 0 ≤ γ u) (hγ1 : ∑ u ∈ V, γ u = 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ Δ : EuclideanSpace ℝ (Fin n) → ℝ, ∃ z ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))),
      (∀ u ∈ V, 0 ≤ Δ u ∧ Δ u ≤ γ u) ∧
      x = ∑ u ∈ V, (γ u - Δ u) • u + (∑ u ∈ V, Δ u) • z ∧
      ∀ u ∈ V, 0 < Δ u → ∃ j, z j = 0 ∧ u j ≠ 0 := by
  classical
  set P := convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) with hPdef
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  let box : EuclideanSpace ℝ (Fin n) → Set ℝ := fun u => if u ∈ V then Set.Icc 0 (γ u) else {0}
  let K : Set ((EuclideanSpace ℝ (Fin n) → ℝ) × EuclideanSpace ℝ (Fin n)) :=
    {p | p.1 ∈ Set.univ.pi box ∧ p.2 ∈ P ∧
      x = ∑ u ∈ V, (γ u - p.1 u) • u + (∑ u ∈ V, p.1 u) • p.2}
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.univ.pi box) := isCompact_univ_pi (fun u => by
      simp only [box]
      split_ifs
      exacts [isCompact_Icc, isCompact_singleton])
    refine (hbox.prod hPc).of_isClosed_subset ?_ (fun p hp => ⟨hp.1, hp.2.1⟩)
    refine ((isClosed_set_pi (fun u _ => ?_)).preimage continuous_fst).inter
      ((hPc.isClosed.preimage continuous_snd).inter (isClosed_eq continuous_const ?_))
    · simp only [box]
      split_ifs
      exacts [isClosed_Icc, isClosed_singleton]
    · fun_prop
  have hK0 : ((fun u => if u ∈ V then γ u else 0), x) ∈ K := by
    refine ⟨fun u _ => ?_, hx, ?_⟩
    · simp only [box]
      split_ifs with hu
      · exact ⟨hγ0 u hu, le_rfl⟩
      · exact rfl
    · have e1 : ∑ u ∈ V, (γ u - (if u ∈ V then γ u else 0)) • u = 0 :=
        Finset.sum_eq_zero (fun u hu => by simp [hu])
      have e2 : ∑ u ∈ V, (if u ∈ V then γ u else 0) = 1 := by
        rw [← hγ1]
        exact Finset.sum_congr rfl (fun u hu => by simp [hu])
      simp only [e1, e2, zero_add, one_smul]
  have hFc : Continuous (fun p : (EuclideanSpace ℝ (Fin n) → ℝ) × EuclideanSpace ℝ (Fin n) =>
      ∑ u ∈ V, p.1 u) := by fun_prop
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨_, hK0⟩ hFc.continuousOn
  have hbox : ∀ u ∈ V, 0 ≤ p.1 u ∧ p.1 u ≤ γ u := fun u hu => by
    have := hpK.1 u (Set.mem_univ u)
    simp only [box, hu, ↓reduceIte] at this
    exact this
  refine ⟨p.1, p.2, hpK.2.1, hbox, hpK.2.2, fun u₀ hu₀ hpos => ?_⟩
  by_contra hcon
  push Not at hcon
  set Δ := p.1 with hΔ
  set z := p.2 with hz
  set S := ∑ u ∈ V, Δ u with hS
  have hS0 : Δ u₀ ≤ S := Finset.single_le_sum (fun u hu => (hbox u hu).1) hu₀
  have hSpos : 0 < S := lt_of_lt_of_le hpos hS0
  have hz0 : ∀ j, 0 ≤ z j := hull_nonneg hP hpK.2.1
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ j, u₀ j ≠ 0 → δ ≤ z j := by
    by_cases hJ : (Finset.univ.filter fun j => u₀ j ≠ 0).Nonempty
    · obtain ⟨j₀, hj₀, hmin⟩ := (Finset.univ.filter fun j => u₀ j ≠ 0).exists_min_image z hJ
      have hj₀' : u₀ j₀ ≠ 0 := (Finset.mem_filter.mp hj₀).2
      exact ⟨z j₀, lt_of_le_of_ne (hz0 j₀) (fun h => hj₀' (hcon j₀ h.symm)),
        fun j hj => hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
    · exact ⟨1, one_pos, fun j hj =>
        absurd ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩ hJ⟩
  set ε := min (Δ u₀ / 2) (S * δ) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (mul_pos hSpos hδpos)
  have hεle : ε ≤ Δ u₀ / 2 := min_le_left _ _
  have hSε : 0 < S - ε := by linarith
  have hcoord : ∀ j, ε * u₀ j ≤ S * z j := fun j => by
    rcases h01 u₀ hu₀ j with h | h
    · rw [h, mul_zero]
      exact mul_nonneg hSpos.le (hz0 j)
    · rw [h, mul_one]
      exact (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (hδ j (by rw [h]; norm_num)) hSpos.le)
  set z' := (S - ε)⁻¹ • (S • z - ε • u₀) with hz'
  have hu₀P : u₀ ∈ P := subset_convexHull ℝ _ (by exact_mod_cast hu₀)
  have hz'P : z' ∈ P := by
    rw [hP]
    refine ⟨fun j => ?_, ?_⟩
    · have : (0 : ℝ) ≤ (S - ε)⁻¹ * (S * z j - ε * u₀ j) :=
        mul_nonneg (inv_nonneg.mpr hSε.le) (by linarith [hcoord j])
      simpa [hz'] using this
    · have hne : S - ε ≠ 0 := hSε.ne'
      have e : z' = AffineMap.lineMap u₀ z (S / (S - ε)) := by
        ext j
        simp only [hz', AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
        field_simp
        ring
      rw [e]
      exact AffineMap.lineMap_mem _ (hull_mem_W hP hu₀P) (hull_mem_W hP hpK.2.1)
  set Δ' := Function.update Δ u₀ (Δ u₀ - ε) with hΔ'
  have hsum' : ∑ u ∈ V, Δ' u = S - ε := by
    rw [hΔ', Finset.sum_update_of_mem hu₀, hS, ← Finset.add_sum_erase V Δ hu₀]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  have hlin : ∑ u ∈ V, (γ u - Δ' u) • u = ∑ u ∈ V, (γ u - Δ u) • u + ε • u₀ := by
    have : ∀ u ∈ V, (γ u - Δ' u) • u = (γ u - Δ u) • u + (if u = u₀ then ε else 0) • u :=
      fun u _ => by
        by_cases h : u = u₀
        · simp only [h, ↓reduceIte, hΔ', Function.update_self]
          rw [← add_smul]
          congr 1
          ring
        · simp only [h, ↓reduceIte, hΔ', Function.update_of_ne h, zero_smul, add_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_eq']
    simp [hu₀]
  have hp'K : (Δ', z') ∈ K := by
    refine ⟨fun u _ => ?_, hz'P, ?_⟩
    · by_cases h : u = u₀
      · rw [h]
        simp only [box, hu₀, ↓reduceIte, hΔ', Function.update_self]
        exact ⟨by linarith, by linarith [(hbox u₀ hu₀).2]⟩
      · simp only [hΔ', Function.update_of_ne h]
        exact hpK.1 u (Set.mem_univ u)
    · show x = ∑ u ∈ V, (γ u - Δ' u) • u + (∑ u ∈ V, Δ' u) • z'
      rw [hlin, hsum', hz', smul_smul, mul_inv_cancel₀ hSε.ne', one_smul]
      have := hpK.2.2
      rw [this]
      abel
  have hmin : ∑ u ∈ V, p.1 u ≤ ∑ u ∈ V, Δ' u := hpmin hp'K
  rw [hsum'] at hmin
  linarith

/-- A Frank–Wolfe vertex is below every point of the hull. -/
theorem ge_on_hull {V : Finset (EuclideanSpace ℝ (Fin n))}
    (ψ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) {v x : EuclideanSpace ℝ (Fin n)}
    (hv : ∀ w ∈ V, ψ v ≤ ψ w) (hx : x ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) :
    ψ v ≤ ψ x := by
  obtain ⟨lam, hlam0, hlam1, hxeq⟩ := Finset.mem_convexHull'.mp hx
  rw [← hxeq, map_sum]
  calc ψ v = ∑ w ∈ V, lam w * ψ v := by rw [← Finset.sum_mul, hlam1, one_mul]
    _ ≤ ∑ w ∈ V, ψ (lam w • w) := Finset.sum_le_sum (fun w hw => by
        rw [map_smul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hv w hw) (hlam0 w hw))

theorem sparsity_scaling : SparsityScaling := by
  intro n V hV x hx y hy ψ a v haV hasupp ha hvV hv
  classical
  obtain ⟨h01, W, hP⟩ := hV
  have hVnn : ∀ u ∈ V, ∀ i, 0 ≤ u i := fun u hu i => by
    rcases h01 u hu i with h | h <;> simp [h]
  obtain ⟨γ, hγ0, hγ1, hyeq⟩ := Finset.mem_convexHull'.mp hy
  obtain ⟨Δ, z, hz, hbox, hxeq, hsupp⟩ := gh_decomposition hP h01 hγ0 hγ1 hx
  set S := ∑ u ∈ V, Δ u with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun u hu => (hbox u hu).1)
  have hxy : x - y = S • z - ∑ u ∈ V, Δ u • u := by
    rw [hxeq, ← hyeq]
    rw [show ∑ u ∈ V, (γ u - Δ u) • u = ∑ u ∈ V, γ u • u - ∑ u ∈ V, Δ u • u by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun u _ => sub_smul _ _ _)]
    abel
  have hxa : ψ x ≤ ψ a := le_of_support hVnn ψ ha hx (fun i hi => hi)
  have hvx : ψ v ≤ ψ x := ge_on_hull ψ hv hx
  have hGa : 0 ≤ ψ (a - v) := by rw [map_sub]; linarith
  have hSz : S * ψ z ≤ S * ψ a := by
    rcases eq_or_lt_of_le hS0 with h0 | hpos
    · rw [← h0]
      simp
    · apply mul_le_mul_of_nonneg_left _ hS0
      apply le_of_support hVnn ψ ha hz
      intro i hi
      have hxi : x i = ∑ u ∈ V, (γ u - Δ u) * u i + S * z i := by rw [hxeq]; simp
      have hterm : 0 ≤ ∑ u ∈ V, (γ u - Δ u) * u i := Finset.sum_nonneg (fun u hu =>
        mul_nonneg (by linarith [(hbox u hu).2]) (hVnn u hu i))
      have hzi : 0 ≤ z i := hull_nonneg hP hz i
      have h1 : S * z i ≤ 0 := by linarith
      exact le_antisymm (by nlinarith) hzi
  have hΔv : S * ψ v ≤ ∑ u ∈ V, Δ u * ψ u := by
    rw [hS, Finset.sum_mul]
    exact Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hv u hu) (hbox u hu).1)
  have hψxy : ψ (x - y) ≤ S * ψ (a - v) := by
    rw [hxy, map_sub, map_smul, map_sum, smul_eq_mul, map_sub]
    simp only [map_smul, smul_eq_mul]
    linarith
  set k := (Finset.univ.filter fun i => y i ≠ 0).card with hk
  set C := Finset.univ.filter fun j => y j ≠ 0 ∧ z j = 0 with hC
  have hCk : C.card ≤ k := Finset.card_le_card (fun j hj => by
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.1)
  have hcoordC : ∀ j ∈ C, (x - y) j = -∑ u ∈ V, Δ u * u j := fun j hj => by
    have hzj : z j = 0 := (Finset.mem_filter.mp hj).2.2
    rw [hxy]
    simp [hzj]
  have hSC : S ≤ ∑ j ∈ C, ∑ u ∈ V, Δ u * u j := by
    rw [Finset.sum_comm, hS]
    apply Finset.sum_le_sum
    intro u hu
    rw [← Finset.mul_sum]
    rcases eq_or_lt_of_le (hbox u hu).1 with h0 | hpos
    · rw [← h0]
      simp
    · obtain ⟨j, hzj, huj⟩ := hsupp u hu hpos
      have huj1 : u j = 1 := (h01 u hu j).resolve_left huj
      have hyj : y j ≠ 0 := by
        have hyj' : y j = ∑ w ∈ V, γ w * w j := by rw [← hyeq]; simp
        have h1 : γ u * u j ≤ ∑ w ∈ V, γ w * w j :=
          Finset.single_le_sum (f := fun w => γ w * w j)
            (fun w hw => mul_nonneg (hγ0 w hw) (hVnn w hw j)) hu
        rw [huj1, mul_one] at h1
        have h2 : 0 < y j := by rw [hyj']; linarith [(hbox u hu).2]
        exact h2.ne'
      have hjC : j ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyj, hzj⟩
      have h3 : u j ≤ ∑ j' ∈ C, u j' :=
        Finset.single_le_sum (f := fun j' => u j') (fun j' _ => hVnn u hu j') hjC
      rw [huj1] at h3
      nlinarith
  have hCS : (∑ j ∈ C, ∑ u ∈ V, Δ u * u j) ^ 2 ≤
      C.card * ∑ j ∈ C, (∑ u ∈ V, Δ u * u j) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hnormC : ∑ j ∈ C, (∑ u ∈ V, Δ u * u j) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j ∈ C, (∑ u ∈ V, Δ u * u j) ^ 2 = ∑ j ∈ C, ‖(x - y) j‖ ^ 2 :=
          Finset.sum_congr rfl (fun j hj => by rw [hcoordC j hj, Real.norm_eq_abs, sq_abs, neg_sq])
      _ ≤ ∑ j, ‖(x - y) j‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg _)
  have hS2 : S ^ 2 ≤ k * ‖x - y‖ ^ 2 := by
    have h1 : S ^ 2 ≤ (∑ j ∈ C, ∑ u ∈ V, Δ u * u j) ^ 2 := pow_le_pow_left₀ hS0 hSC 2
    have h2 : (C.card : ℝ) ≤ k := by exact_mod_cast hCk
    calc S ^ 2 ≤ _ := h1
      _ ≤ C.card * ∑ j ∈ C, (∑ u ∈ V, Δ u * u j) ^ 2 := hCS
      _ ≤ k * ‖x - y‖ ^ 2 := mul_le_mul h2 hnormC
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hSle : S ≤ √k * ‖x - y‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (x - y)), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact (le_abs_self S).trans (Real.abs_le_sqrt hS2)
  calc ψ (x - y) ≤ S * ψ (a - v) := hψxy
    _ ≤ √k * ‖x - y‖ * ψ (a - v) := mul_le_mul_of_nonneg_right hSle hGa

theorem dipfw_feasible_aux {V : Finset (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hV : IsSimplexLike V) (hγ : ∀ t, 1 ≤ t → ∃ m : ℕ, γ t = (1 / 2) ^ m)
    (hmono : ∀ t, 1 ≤ t → γ (t + 1) ≤ γ t) (hrun : IsDIPFWRun V f γ x) :
    ∀ t, 1 ≤ t → x t ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) ∧
      ∀ i, ∃ s : ℕ, x t i = γ t * s := by
  obtain ⟨h01, W, hP⟩ := hV
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    refine ⟨subset_convexHull ℝ _ (by exact_mod_cast hrun.2.1), fun i => ?_⟩
    obtain ⟨m, hm⟩ := hγ 1 le_rfl
    rcases h01 _ hrun.2.1 i with h | h
    · exact ⟨0, by rw [h]; simp⟩
    · refine ⟨2 ^ m, ?_⟩
      rw [h, hm]
      push_cast
      rw [← mul_pow]
      norm_num
  | succ t ht ih =>
    obtain ⟨hxt, hs⟩ := ih
    obtain ⟨v, hvV, -, a, haV, hasupp, -, hx'⟩ := hrun.2.2.2 t ht
    obtain ⟨m, hm⟩ := hγ t ht
    obtain ⟨m', hm'⟩ := hγ (t + 1) (by omega)
    have hmm : m ≤ m' := by
      have := hmono t ht
      rw [hm, hm'] at this
      exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mp this
    have hcoord : ∀ i, ∃ s : ℕ, x (t + 1) i = γ t * s := fun i => by
      obtain ⟨s, hsi⟩ := hs i
      have hxi : x (t + 1) i = x t i + γ t * (v i - a i) := by rw [hx']; simp
      rcases h01 v hvV i with hv | hv <;> rcases h01 a haV i with ha | ha
      · exact ⟨s, by rw [hxi, hsi, hv, ha]; ring⟩
      · have hs1 : 1 ≤ s := by
          rcases Nat.eq_zero_or_pos s with h0 | h0
          · exfalso
            have := hasupp i (by rw [hsi, h0]; simp)
            rw [ha] at this
            norm_num at this
          · exact h0
        exact ⟨s - 1, by rw [hxi, hsi, hv, ha, Nat.cast_sub hs1]; push_cast; ring⟩
      · exact ⟨s + 1, by rw [hxi, hsi, hv, ha]; push_cast; ring⟩
      · exact ⟨s, by rw [hxi, hsi, hv, ha]; ring⟩
    have hγpos : 0 < γ t := by rw [hm]; positivity
    refine ⟨?_, fun i => ?_⟩
    · rw [hP]
      refine ⟨fun i => ?_, ?_⟩
      · obtain ⟨s, hsi⟩ := hcoord i
        rw [hsi]
        positivity
      · rw [hx']
        have hxW := hull_mem_W hP hxt
        have hvW := hull_mem_W hP (subset_convexHull ℝ _ (by exact_mod_cast hvV))
        have haW := hull_mem_W hP (subset_convexHull ℝ _ (by exact_mod_cast haV))
        have h1 : γ t • (v -ᵥ a) +ᵥ x t ∈ W := AffineSubspace.vadd_mem_of_mem_direction
          (Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hvW haW)) hxW
        simpa [vsub_eq_sub, vadd_eq_add, add_comm] using h1
    · obtain ⟨s, hsi⟩ := hcoord i
      obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
      refine ⟨2 ^ d * s, ?_⟩
      rw [hsi, hm, hm']
      push_cast
      have h2 : ((1 : ℝ) / 2) ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
      calc ((1 : ℝ) / 2) ^ m * s = (1 / 2) ^ m * ((1 / 2) ^ d * 2 ^ d) * s := by rw [h2, mul_one]
        _ = (1 / 2) ^ (m + d) * (2 ^ d * s) := by rw [pow_add]; ring

theorem dipfw_feasible : DIPFWFeasible := by
  intro n V f γ x hV hγ hmono hrun t
  rcases Nat.eq_zero_or_pos t with h0 | ht
  · rw [h0]
    exact hrun.1
  · exact (dipfw_feasible_aux hV hγ hmono hrun t ht).1

end Proof

end Lemmata.AwayStepFW
