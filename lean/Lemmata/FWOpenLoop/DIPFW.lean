module

public import Lemmata.FWOpenLoop.SeqGen
public import Lemmata.AwayStepFW.SimplexLike
public import Lemmata.FrankWolfe.Proof.Run

@[expose] public section

/-!
# Decomposition-invariant pairwise Frank–Wolfe with open-loop step sizes

Proposition 5.2 and Theorem 5.3. The step sizes `γ_t` are the largest powers of `1/2` below
`η_t = 8/(t + 8)`, so they are nonincreasing and the run stays feasible (Garber and Meshi). A
pairwise step gains `γ_t f'(x_t)(a_t - v_t) ≥ (η_t/2) f'(x_t)(a_t - v_t)`, and this pairwise gap is
at least the primal gap and, by the sparsity scaling, at least `h_t^{1-θ}/(μ √‖x⋆‖₀)`.
-/

namespace Lemmata.FWOpenLoop

open Lemmata.FrankWolfe

variable {n : ℕ}

/-- The largest powers of `1/2` below `η_t = 8/(t + 8)` are nonincreasing. -/
theorem dyadic_antitone {γ : ℕ → ℝ}
    (hγ : ∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t) :
    ∀ t, 1 ≤ t → γ (t + 1) ≤ γ t := by
  intro t ht
  obtain ⟨⟨m, hm⟩, hlo, -⟩ := hγ t ht
  obtain ⟨⟨m', hm'⟩, -, hhi'⟩ := hγ (t + 1) (by omega)
  have hη : eta 8 ((t + 1 : ℕ) : ℤ) ≤ eta 8 (t : ℤ) := by
    have := etaL_anti (ℓ := 8) (by norm_num) ((t + 1 : ℕ) : ℤ) (by omega)
    rwa [show ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) by push_cast; ring] at this
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have hmm : m' < m := by
    rw [hm, hm'] at hlt
    by_contra hge
    have : (1 / 2 : ℝ) ^ m' ≤ (1 / 2) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.mp hge)
    linarith
  have h2 : 2 * γ t ≤ γ (t + 1) := by
    rw [hm, hm']
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have : (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ m' :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ]
    linarith
  have h3 : γ (t + 1) ≤ eta 8 ((t + 1 : ℕ) : ℤ) := hhi'
  linarith

/-- One step of the run: the pairwise gap `G_t = f'(x_t)(a_t - v_t)` bounds the primal gap and
the progress `h_{t+1} ≤ h_t - (η_t/2) G_t + η_t² L δ²/2` holds. -/
theorem dipfw_step {V : Finset (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ} {γ : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} (hV : AwayStepFW.IsSimplexLike V)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L) (hL : 0 ≤ L)
    (hγ : ∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t)
    (hrun : AwayStepFW.IsDIPFWRun V f γ x) {xStar : EuclideanSpace ℝ (Fin n)}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ G : ℝ, f (x t) - f xStar ≤ G ∧
      f (x (t + 1)) - f xStar ≤ (f (x t) - f xStar) - eta 8 t / 2 * G +
        eta 8 t ^ 2 * (L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 /
          2) ∧
      ((f xStar < f (x t)) → ∀ μ θ : ℝ, 0 < μ →
        IsHolderErrorBound (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f μ θ →
        minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f = {xStar} →
        (f (x t) - f xStar) ^ (1 - θ) ≤
          μ * √((Finset.univ.filter fun i => xStar i ≠ 0).card : ℝ) * G) := by
  classical
  set P := convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) with hPdef
  set δ := Metric.diam P with hδ
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hfeas : ∀ t, x t ∈ P := Lemmata.AwayStepFW.Proof.dipfw_feasible n V f γ x hV
    (fun t ht => (hγ t ht).1) (dyadic_antitone hγ) hrun
  obtain ⟨h01, W, hP⟩ := hV
  have hVnn : ∀ u ∈ V, ∀ i, 0 ≤ u i := fun u hu i => by
    rcases h01 u hu i with h | h <;> simp [h]
  obtain ⟨-, hγlo, hγhi⟩ := hγ t ht
  obtain ⟨v, hvV, hv, a, haV, hasupp, ha, hx'⟩ := hrun.2.2.2 t ht
  set g := fderiv ℝ f (x t) with hg
  set G := g (a - v) with hG
  have hvP : v ∈ P := subset_convexHull ℝ _ (Finset.mem_coe.mpr hvV)
  have haP : a ∈ P := subset_convexHull ℝ _ (Finset.mem_coe.mpr haV)
  have hη0 : 0 < eta 8 t := etaL_pos (ℓ := 8) (by norm_num) _ (by omega)
  -- the primal gap is at most the pairwise gap
  have hxa : g (x t) ≤ g a :=
    Lemmata.AwayStepFW.Proof.le_of_support hVnn g ha (hfeas t) (fun i hi => hi)
  have hvx : g v ≤ g xStar := Lemmata.AwayStepFW.Proof.ge_on_hull g hv hxs.1
  have hcvx := convexOn_add_fderiv_le hconv (hfeas t) (hdiff _ (hfeas t)) hxs.1
  have hlin : g (xStar - x t) = g xStar - g (x t) := map_sub _ _ _
  have hGeq : G = g a - g v := map_sub _ _ _
  have hgap : f (x t) - f xStar ≤ G := by rw [← hg] at hcvx; linarith
  refine ⟨G, hgap, ?_, ?_⟩
  · have h1 := hsm (x t) (hfeas t) (x (t + 1)) (hfeas (t + 1))
    have hd : x (t + 1) - x t = γ t • (v - a) := by rw [hx']; abel
    rw [hd, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
    have h2 : ‖v - a‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hPc.isBounded hvP haP
    have h3 : fderiv ℝ f (x t) (v - a) = -G := by rw [hG, ← hg, map_sub, map_sub]; ring
    rw [h3] at h1
    have hG0 : 0 ≤ G := le_trans (sub_nonneg.mpr (hxs.2 _ (hfeas t))) hgap
    have h4 : γ t ^ 2 * ‖v - a‖ ^ 2 ≤ eta 8 t ^ 2 * δ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h2 2
      have := pow_le_pow_left₀ (by linarith) hγhi 2
      nlinarith [sq_nonneg (γ t), sq_nonneg δ]
    have h5 : eta 8 t / 2 * G ≤ γ t * G := mul_le_mul_of_nonneg_right hγlo.le hG0
    have h6 : L / 2 * (γ t ^ 2 * ‖v - a‖ ^ 2) ≤ L / 2 * (eta 8 t ^ 2 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  · intro hlt μ θ hμ heb huniq
    have hsc := Lemmata.AwayStepFW.Proof.sparsity_scaling n V ⟨h01, W, hP⟩ (x t) (hfeas t) xStar
      hxs.1 g a v haV hasupp ha hvV hv
    have hgx : f (x t) - f xStar ≤ g (x t - xStar) := by
      have : g (x t - xStar) = g (x t) - g xStar := map_sub _ _ _
      rw [← hg] at hcvx; linarith
    have hdist : ‖x t - xStar‖ ≤ μ * (f (x t) - f xStar) ^ θ := by
      have := heb (x t) (hfeas t) xStar hxs
      rwa [huniq, Metric.infDist_singleton, dist_eq_norm] at this
    set h := f (x t) - f xStar with hh
    have hpos : 0 < h := by rw [hh]; linarith
    set k := √((Finset.univ.filter fun i => xStar i ≠ 0).card : ℝ) with hk
    have hk0 : 0 ≤ k := Real.sqrt_nonneg _
    have hG0 : 0 ≤ G := le_trans hpos.le hgap
    -- `h ≤ k ‖x - x⋆‖ G ≤ k μ h^θ G`
    have h1 : h ≤ k * (μ * h ^ θ) * G := by
      calc h ≤ g (x t - xStar) := hgx
        _ ≤ k * ‖x t - xStar‖ * G := hsc
        _ ≤ k * (μ * h ^ θ) * G := by
          apply mul_le_mul_of_nonneg_right _ hG0
          exact mul_le_mul_of_nonneg_left hdist hk0
    have hsplit : h ^ (1 - θ) * h ^ θ = h := by
      rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
    have hθpos : 0 < h ^ θ := Real.rpow_pos_of_pos hpos θ
    have : h ^ (1 - θ) * h ^ θ ≤ (μ * k * G) * h ^ θ := by
      rw [hsplit]; nlinarith
    exact le_of_mul_le_mul_right this hθpos

/-- The first iterate is a Frank–Wolfe vertex, so `h₁ ≤ L δ²/2`. -/
theorem dipfw_first {V : Finset (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ} {γ : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} (hV : AwayStepFW.IsSimplexLike V)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L) (hL : 0 ≤ L)
    (hγ : ∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t)
    (hrun : AwayStepFW.IsDIPFWRun V f γ x) {xStar : EuclideanSpace ℝ (Fin n)}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f) :
    f (x 1) - f xStar ≤
      L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 / 2 := by
  set P := convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) with hPdef
  have hPc : IsCompact P := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hfeas : ∀ t, x t ∈ P := Lemmata.AwayStepFW.Proof.dipfw_feasible n V f γ x hV
    (fun t ht => (hγ t ht).1) (dyadic_antitone hγ) hrun
  set g := fderiv ℝ f (x 0) with hg
  have h1 := hsm (x 0) (hfeas 0) (x 1) (hfeas 1)
  have h2 : g (x 1) ≤ g xStar := Lemmata.AwayStepFW.Proof.ge_on_hull g hrun.2.2.1 hxs.1
  have h3 := convexOn_add_fderiv_le hconv (hfeas 0) (hdiff _ (hfeas 0)) hxs.1
  have h4 : ‖x 1 - x 0‖ ≤ Metric.diam P := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hPc.isBounded (hfeas 1) (hfeas 0)
  have h5 : L / 2 * ‖x 1 - x 0‖ ^ 2 ≤ L / 2 * Metric.diam P ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h4 2) (by positivity)
  have e1 : g (x 1 - x 0) = g (x 1) - g (x 0) := map_sub _ _ _
  have e2 : g (xStar - x 0) = g xStar - g (x 0) := map_sub _ _ _
  rw [← hg] at h1 h3
  linarith

/-- **Proposition 5.2.** -/
theorem dipfw_baseline_bound {V : Finset (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} {γ : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hV : AwayStepFW.IsSimplexLike V)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L) (hL : 0 ≤ L)
    (hγ : ∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t)
    (hrun : AwayStepFW.IsDIPFWRun V f γ x) {xStar : EuclideanSpace ℝ (Fin n)}
    (hxs : xStar ∈ minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      32 * L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 / (t + 7) := by
  set δ := Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) with hδ
  have hK : 0 ≤ L * δ ^ 2 := by positivity
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    have := dipfw_first hV hconv hdiff hsm hL hγ hrun hxs
    push_cast
    nlinarith
  | succ t ht ih =>
    obtain ⟨G, hgap, hprog, -⟩ := dipfw_step hV hconv hdiff hsm hL hγ hrun hxs t ht
    have hη : eta 8 (t : ℤ) = 8 / ((t : ℝ) + 8) := by simp [eta]
    rw [hη, ← hδ] at hprog
    have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hη0 : 0 ≤ 8 / ((t : ℝ) + 8) := by positivity
    have h1 : f (x (t + 1)) - f xStar ≤ (1 - 4 / ((t : ℝ) + 8)) * (f (x t) - f xStar) +
        (8 / ((t : ℝ) + 8)) ^ 2 * (L * δ ^ 2 / 2) := by
      have := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ 8 / ((t : ℝ) + 8) / 2)
      have e : 8 / ((t : ℝ) + 8) / 2 = 4 / ((t : ℝ) + 8) := by ring
      rw [e] at this hprog
      nlinarith
    have hcoef : 0 ≤ 1 - 4 / ((t : ℝ) + 8) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left ih hcoef
    push_cast
    have ht8 : (0 : ℝ) < t + 8 := by positivity
    have ht7 : (0 : ℝ) < t + 7 := by positivity
    have key0 : ((t : ℝ) + 4) / ((t + 8) * (t + 7)) + 1 / (t + 8) ^ 2 ≤ 1 / (t + 8) := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) ht8]
      have ht0' : (0 : ℝ) ≤ t := by positivity
      nlinarith [mul_nonneg ht0' (sq_nonneg ((t : ℝ) + 8)), sq_nonneg ((t : ℝ) + 8),
        mul_nonneg (mul_nonneg ht0' ht0') ht0']
    have key := mul_le_mul_of_nonneg_left key0 (by positivity : (0 : ℝ) ≤ 32 * (L * δ ^ 2))
    have e1 : (1 - 4 / ((t : ℝ) + 8)) * (32 * L * δ ^ 2 / (t + 7)) =
        32 * (L * δ ^ 2) * (((t : ℝ) + 4) / ((t + 8) * (t + 7))) := by
      field_simp; ring
    have e2 : (8 / ((t : ℝ) + 8)) ^ 2 * (L * δ ^ 2 / 2) = 32 * (L * δ ^ 2) * (1 / (t + 8) ^ 2) := by
      field_simp; ring
    have e3 : 32 * L * δ ^ 2 / ((t : ℝ) + 1 + 7) = 32 * (L * δ ^ 2) * (1 / (t + 8)) := by
      rw [show (t : ℝ) + 1 + 7 = t + 8 by ring]; ring
    rw [e3]
    nlinarith

/-- **Theorem 5.3.** -/
theorem dipfw_rate_bound {V : Finset (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L μ θ : ℝ} {γ : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {xStar : EuclideanSpace ℝ (Fin n)} (hV : AwayStepFW.IsSimplexLike V)
    (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f L) (hL : 0 < L)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))))
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f μ θ)
    (hμ : 0 < μ) (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2))
    (huniq : minimizers (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) f = {xStar})
    (hγ : ∀ t : ℕ, 1 ≤ t → (∃ m : ℕ, γ t = (1 / 2) ^ m) ∧ eta 8 t / 2 < γ t ∧ γ t ≤ eta 8 t)
    (hrun : AwayStepFW.IsDIPFWRun V f γ x) :
    ∀ t : ℕ, 1 ≤ t → f (x t) - f xStar ≤
      max (eta 8 ((t : ℤ) - 2) ^ (1 / (1 - θ)) *
          (L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 / 2))
        ((eta 8 ((t : ℤ) - 2) * (2 * μ * L *
            Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 *
            √((Finset.univ.filter fun i => xStar i ≠ 0).card : ℝ))) ^ (1 / (1 - θ)) +
          eta 8 ((t : ℤ) - 2) ^ 2 *
            (L * Metric.diam (convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n)))) ^ 2 / 2)) := by
  set P := convexHull ℝ (↑V : Set (EuclideanSpace ℝ (Fin n))) with hPdef
  set δ := Metric.diam P with hδ
  set kk := √((Finset.univ.filter fun i => xStar i ≠ 0).card : ℝ) with hkk
  have hxs : xStar ∈ minimizers P f := by rw [huniq]; rfl
  have hfeas : ∀ t, x t ∈ P := Lemmata.AwayStepFW.Proof.dipfw_feasible n V f γ x hV
    (fun t ht => (hγ t ht).1) (dyadic_antitone hγ) hrun
  have hh0 : ∀ t, 0 ≤ f (x t) - f xStar := fun t => sub_nonneg.mpr (hxs.2 _ (hfeas t))
  have hθ1 : θ < 1 := by linarith [hθ.2]
  set B := L * δ ^ 2 / 2 with hB
  have hBpos : 0 < B := by positivity
  intro t ht
  have hmax0 : 0 ≤ eta 8 ((t : ℤ) - 2) ^ (1 / (1 - θ)) * B :=
    mul_nonneg (Real.rpow_nonneg (etaL_pos (by norm_num) _ (by omega)).le _) hBpos.le
  rcases (Real.sqrt_nonneg _ : (0 : ℝ) ≤ kk).eq_or_lt with hk0 | hkpos
  · -- no nonzero coordinate: every iterate after the first is optimal
    have hzero : f (x t) - f xStar ≤ 0 := by
      by_contra hpos
      replace hpos := lt_of_not_ge hpos
      obtain ⟨G, -, -, hsc⟩ := dipfw_step hV hconv hdiff hsm hL.le hγ hrun hxs t ht
      have := hsc (by linarith) μ θ hμ heb huniq
      rw [← hk0, mul_zero, zero_mul] at this
      have : 0 < (f (x t) - f xStar) ^ (1 - θ) := Real.rpow_pos_of_pos hpos _
      linarith
    exact le_trans hzero (le_max_of_le_left hmax0)
  set A := 1 / (4 * μ * kk) with hA
  have hApos : 0 < A := by positivity
  have hrec : ∀ τ, 1 ≤ τ → f (x (τ + 1)) - f xStar ≤
      (1 - 2 / 8 * eta 8 τ) * (f (x τ) - f xStar) -
        eta 8 τ * A * 1 * (f (x τ) - f xStar) ^ (1 - θ) + eta 8 τ ^ 2 * B * 1 := by
    intro τ hτ
    obtain ⟨G, hgap, hprog, hsc⟩ := dipfw_step hV hconv hdiff hsm hL.le hγ hrun hxs τ hτ
    rw [← hPdef, ← hδ, ← hB] at hprog
    have hη : 0 ≤ eta 8 τ := (etaL_pos (by norm_num) _ (by omega)).le
    have hG4 : 4 * A * (f (x τ) - f xStar) ^ (1 - θ) ≤ G := by
      rcases (hh0 τ).eq_or_lt with h0 | hpos
      · have h00 : (f (x τ) - f xStar) ^ (1 - θ) = 0 := by
          rw [← h0]; exact Real.zero_rpow (by linarith : (0 : ℝ) < 1 - θ).ne'
        rw [h00, mul_zero]; linarith [hh0 τ]
      · have := hsc (by linarith) μ θ hμ heb huniq
        have e : 4 * A = 1 / (μ * kk) := by rw [hA]; field_simp
        rw [e, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith
    have hG : (f (x τ) - f xStar) / 2 + 2 * A * (f (x τ) - f xStar) ^ (1 - θ) ≤ G := by
      linarith
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ eta 8 τ / 2)
    linarith
  -- the invariant of the sequence lemma along the run
  set e := 1 / (2 * (1 - θ)) with he
  set Q := eta 8 (((1 : ℕ) : ℤ) - 2) * eta 8 (((1 : ℕ) : ℤ) - 1) with hQ
  have hQpos : 0 < Q := mul_pos (etaL_pos (by norm_num) _ (by omega))
    (etaL_pos (by norm_num) _ (by omega))
  have hinv : ∀ τ, 1 ≤ τ → f (x τ) - f xStar ≤ max (seqX 8 e Q B τ) (seqY 8 e A B 1 τ) := by
    intro τ hτ
    induction τ, hτ using Nat.le_induction with
    | base =>
      refine le_max_of_le_left ?_
      simp only [seqX]
      rw [← hQ, div_self hQpos.ne', Real.one_rpow, one_mul]
      exact dipfw_first hV hconv hdiff hsm hL.le hγ hrun hxs
    | succ τ hτ ih =>
      exact seq_step τ (by norm_num) hθ hApos hBpos one_pos hQpos hBpos.le ⟨zero_le_one, le_rfl⟩
        (hh0 τ) (hrec τ hτ) ih
  have hfin := seq_final (ℓ := 8) (ψ := θ) (A := A) (B := B) (C := 1) (K₀ := B) 1 t
    (by norm_num) hθ hApos hBpos one_pos hBpos.le le_rfl
  have hη1 : eta 8 (((1 : ℕ) : ℤ) - 1) = 1 := by simp [eta]
  have hBA : eta 8 ((t : ℤ) - 2) * B / A = eta 8 ((t : ℤ) - 2) * (2 * μ * L * δ ^ 2 * kk) := by
    rw [hA, hB]; field_simp; ring
  refine le_trans (hinv t ht) (le_trans hfin (le_of_eq ?_))
  rw [hη1, div_one, hBA, mul_one]

namespace Proof

theorem dipfw_baseline : DIPFWBaseline := by
  intro n V f L γ x hV hconv hdiff hsm hL hγ hrun xStar hxs t ht
  exact dipfw_baseline_bound hV hconv hdiff hsm hL hγ hrun hxs t ht

theorem dipfw_open_loop_rate : DIPFWOpenLoopRate := by
  intro n V f L μ θ γ x xStar hV hconv hdiff hsm hL hdiam heb hμ hθ huniq hγ hrun δ k t ht
  exact dipfw_rate_bound hV hconv hdiff hsm hL hdiam heb hμ hθ huniq hγ hrun t ht

end Proof

end Lemmata.FWOpenLoop
