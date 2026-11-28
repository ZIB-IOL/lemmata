module

public import Lemmata.FWAffineOpenLoop.Gaps
public import Lemmata.FWAffineOpenLoop.Sufficient

@[expose] public section

/-!
# The optimal face of a polytope (Section 5.2)

Lemma 5.6: once the atoms lie in a convex set `K`, the open-loop steps contract the distance to
`K` by `1 - η_t`, and `(1 - η_t) η_t² ≤ η_{t+1}²` for `ℓ ≥ 2` gives
`dist(x_t, K) ≤ (η_t/η_Q)² dist(x_Q, K)`. Lemma 5.7 identifies the active face from the baseline
rate `h_t ≤ η_t L D²` of Theorem 3.1. Proposition 5.4 compares the gap at `x_t` with the gap at a
nearest point `x̄_t` of the optimal face, where Proposition 5.3 applies.
-/

namespace Lemmata.FWAffineOpenLoop

open Lemmata.FrankWolfe Lemmata.FWOpenLoop

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eta_nat_pos (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℕ) : 0 < eta ℓ (t : ℤ) := by
  rw [eta_nat]
  have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  positivity

theorem eta_nat_anti (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {s t : ℕ} (hst : s ≤ t) :
    eta ℓ (t : ℤ) ≤ eta ℓ (s : ℤ) := by
  rw [eta_nat, eta_nat]
  have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have : (s : ℝ) ≤ t := by exact_mod_cast hst
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- `(1 - η_t) η_t² ≤ η_{t+1}²` for `η_t = ℓ/(t + ℓ)` with `ℓ ≥ 2`. -/
theorem eta_sq_step (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (t : ℕ) :
    (1 - eta ℓ (t : ℤ)) * eta ℓ (t : ℤ) ^ 2 ≤ eta ℓ ((t + 1 : ℕ) : ℤ) ^ 2 := by
  rw [eta_nat, eta_nat]
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have ht : (0 : ℝ) ≤ t := by positivity
  push_cast
  have h1 : (0 : ℝ) < t + ℓ := by linarith
  have h2 : (0 : ℝ) < t + 1 + ℓ := by linarith
  have key : (t : ℝ) * (t + 1 + ℓ) ^ 2 ≤ (t + ℓ) ^ 3 := by
    have e : ((t : ℝ) + ℓ) ^ 3 - t * (t + 1 + ℓ) ^ 2 =
        (ℓ - 2) * (t + ℓ) ^ 2 + (2 * ℓ - 1) * (t + ℓ) + ℓ := by ring
    have : 0 ≤ ((ℓ : ℝ) - 2) * (t + ℓ) ^ 2 + (2 * ℓ - 1) * (t + ℓ) + ℓ := by
      have a1 : 0 ≤ ((ℓ : ℝ) - 2) * (t + ℓ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have a2 : 0 ≤ (2 * (ℓ : ℝ) - 1) * (t + ℓ) := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  rw [div_pow, div_pow, one_sub_div h1.ne', div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left key (sq_nonneg (ℓ : ℝ))
  nlinarith [this]

/-- One step with its atom in a convex set `K` contracts the distance to `K` by `1 - η`. -/
theorem infDist_step {K : Set E} (hK : Convex ℝ K) {x x' v : E} {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ K) (hx' : x' = x + η • (v - x)) :
    Metric.infDist x' K ≤ (1 - η) * Metric.infDist x K := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · simp [hK0]
  have h1η : 0 ≤ 1 - η := by linarith [hη.2]
  rcases eq_or_lt_of_le h1η with h0 | hpos
  · have hη1 : η = 1 := by linarith
    have hx'v : x' = v := by rw [hx', hη1, one_smul, add_sub_cancel]
    rw [← h0, zero_mul, hx'v]
    exact (Metric.infDist_zero_of_mem hv).le
  · have hle : Metric.infDist x' K / (1 - η) ≤ Metric.infDist x K := by
      rw [Metric.le_infDist hKne]
      intro y hy
      rw [div_le_iff₀ hpos]
      have hz : (1 - η) • y + η • v ∈ K := hK hy hv h1η hη.1 (by ring)
      calc Metric.infDist x' K ≤ dist x' ((1 - η) • y + η • v) :=
            Metric.infDist_le_dist_of_mem hz
        _ = (1 - η) * dist x y := by
          rw [hx', dist_eq_norm, dist_eq_norm,
            show x + η • (v - x) - ((1 - η) • y + η • v) = (1 - η) • (x - y) by module,
            norm_smul, Real.norm_of_nonneg h1η]
        _ = dist x y * (1 - η) := by ring
    rwa [div_le_iff₀ hpos, mul_comm] at hle

/-- **Lemma 5.6.** -/
theorem dist_active_bound {C K : Set E} {f' : E → StrongDual ℝ E} {ℓ Q : ℕ} {x v : ℕ → E}
    (hK : Convex ℝ K) (hℓ : 2 ≤ ℓ) (hrun : IsFWRun C f' x v (fun t => eta ℓ t))
    (hvK : ∀ t, Q ≤ t → v t ∈ K) :
    ∀ t : ℕ, Q ≤ t →
      Metric.infDist (x t) K ≤ (eta ℓ t / eta ℓ Q) ^ 2 * Metric.infDist (x Q) K := by
  have hQ := eta_nat_pos ℓ (by omega) Q
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [div_self hQ.ne', one_pow, one_mul]
  | succ t ht ih =>
    obtain ⟨-, -, hη, hx⟩ := hrun.2 t
    have h1 := infDist_step hK hη (hvK t ht) hx
    have h2 := eta_sq_step ℓ hℓ t
    have h0 : 0 ≤ Metric.infDist (x Q) K := Metric.infDist_nonneg
    have hη1 : 0 ≤ 1 - eta ℓ (t : ℤ) := by linarith [hη.2]
    calc Metric.infDist (x (t + 1)) K ≤ (1 - eta ℓ t) * Metric.infDist (x t) K := h1
      _ ≤ (1 - eta ℓ t) * ((eta ℓ t / eta ℓ Q) ^ 2 * Metric.infDist (x Q) K) :=
          mul_le_mul_of_nonneg_left ih hη1
      _ = (1 - eta ℓ t) * eta ℓ t ^ 2 / eta ℓ Q ^ 2 * Metric.infDist (x Q) K := by
          rw [div_pow]; ring
      _ ≤ eta ℓ ((t + 1 : ℕ) : ℤ) ^ 2 / eta ℓ Q ^ 2 * Metric.infDist (x Q) K := by
          gcongr
      _ = (eta ℓ ((t + 1 : ℕ) : ℤ) / eta ℓ Q) ^ 2 * Metric.infDist (x Q) K := by
          rw [div_pow]

/-- **Lemma 5.7.** -/
theorem active_set_ell {V F : Finset E} {f : E → ℝ} {L μ θ κ : ℝ} {ℓ : ℕ} {x v : ℕ → E}
    {xStar : E} (hFV : F ⊆ V) (hconv : ConvexOn ℝ (convexHull ℝ (↑V : Set E)) f)
    (hdiff : ∀ y ∈ convexHull ℝ (↑V : Set E), DifferentiableAt ℝ f y)
    (hsm : IsSmoothOn (convexHull ℝ (↑V : Set E)) f L) (hL : 0 < L)
    (hlip : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E),
      ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hdiam : 0 < Metric.diam (convexHull ℝ (↑V : Set E)))
    (huniq : minimizers (convexHull ℝ (↑V : Set E)) f = {xStar})
    (heb : IsHolderErrorBound (convexHull ℝ (↑V : Set E)) f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hκ : 0 < κ)
    (hsc1 : ∀ p ∈ V, p ∉ F → κ ≤ fderiv ℝ f xStar (p - xStar))
    (hsc0 : ∀ p ∈ F, fderiv ℝ f xStar (p - xStar) = 0) (hℓ : 2 ≤ ℓ)
    (hrun : IsFWRun (convexHull ℝ (↑V : Set E)) (fderiv ℝ f) x v (fun t => eta ℓ t)) :
    ∀ t : ℕ, ⌈(ℓ : ℝ) * L * Metric.diam (convexHull ℝ (↑V : Set E)) ^ 2 *
        (2 * μ * L * Metric.diam (convexHull ℝ (↑V : Set E)) / κ) ^ (1 / θ)⌉₊ ≤ t →
      v t ∈ convexHull ℝ (↑F : Set E) := by
  classical
  intro t ht
  set C := convexHull ℝ (↑V : Set E) with hCdef
  set δ := Metric.diam C with hδ
  have hC : IsCompact C := V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hxs : xStar ∈ minimizers C f := by rw [huniq]; rfl
  have hθ0 := hθ.1
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set c := 2 * μ * L * δ / κ with hc
  have hcpos : 0 < c := by positivity
  have hS : 0 < (ℓ : ℝ) * L * δ ^ 2 * c ^ (1 / θ) := by positivity
  have ht1 : 1 ≤ t := le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hS).ne') ht
  have hxC : x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hconv.1 hrun t
  have hsg : IsStrongGrowth C f (L * δ ^ 2) 0 :=
    Proof.smooth_strong_growth C f L (convex_convexHull ℝ _) hC.isBounded hL.le hsm
  have hb : f (x t) - f xStar ≤ eta ℓ t * (L * δ ^ 2) :=
    (pd_ge_subopt hconv hdiff hxs hrun t).trans
      (pd_rate_zero_bound (convex_convexHull ℝ _) (by positivity) hℓ hsg hrun t ht1)
  rw [eta_nat] at hb
  set h := f (x t) - f xStar with hh
  have hh0 : 0 ≤ h := sub_nonneg.mpr (hxs.2 _ hxC)
  have hlt : h < (1 / c) ^ (1 / θ) := by
    have h1 : (ℓ : ℝ) * L * δ ^ 2 * c ^ (1 / θ) ≤ t :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast ht)
    have hinv : (1 / c) ^ (1 / θ) * c ^ (1 / θ) = 1 := by
      rw [← Real.mul_rpow (by positivity) hcpos.le, one_div_mul_cancel hcpos.ne', Real.one_rpow]
    have h2 : (ℓ : ℝ) / (t + ℓ) * (L * δ ^ 2) < (1 / c) ^ (1 / θ) := by
      have htl : (0 : ℝ) < t + ℓ := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ htl]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / c) ^ (1 / θ))
      have e : (1 / c) ^ (1 / θ) * ((ℓ : ℝ) * L * δ ^ 2 * c ^ (1 / θ)) = ℓ * (L * δ ^ 2) := by
        rw [mul_left_comm, hinv, mul_one]; ring
      have hpos : 0 < (1 / c) ^ (1 / θ) := by positivity
      nlinarith [mul_pos hpos (by linarith : (0 : ℝ) < ℓ)]
    linarith
  have hpow : h ^ θ < 1 / c := by
    have := Real.rpow_lt_rpow hh0 hlt hθ0
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ0.ne', Real.rpow_one] at this
  have hdist : ‖x t - xStar‖ ≤ μ * h ^ θ := by
    have := heb (x t) hxC xStar hxs
    rwa [huniq, Metric.infDist_singleton, dist_eq_norm] at this
  have hgrad := hlip (x t) hxC xStar hxs.1
  have hκ2 : L * δ * (μ * h ^ θ) < κ / 2 := by
    have : L * δ * (μ * h ^ θ) < L * δ * (μ * (1 / c)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hpow hμ) (by positivity)
    have e : L * δ * (μ * (1 / c)) = κ / 2 := by rw [hc]; field_simp
    linarith
  have hkey : ∀ p ∈ C, |(fderiv ℝ f (x t) - fderiv ℝ f xStar) (p - x t)| < κ / 2 := by
    intro p hp
    have hpd : ‖p - x t‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hC.isBounded hp hxC
    calc |(fderiv ℝ f (x t) - fderiv ℝ f xStar) (p - x t)|
        ≤ ‖fderiv ℝ f (x t) - fderiv ℝ f xStar‖ * ‖p - x t‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * (μ * h ^ θ)) * δ := by
          apply mul_le_mul (le_trans hgrad (mul_le_mul_of_nonneg_left hdist hL.le)) hpd
            (norm_nonneg _) (by positivity)
      _ = L * δ * (μ * h ^ θ) := by ring
      _ < κ / 2 := hκ2
  set g := fderiv ℝ f (x t) with hg
  set gs := fderiv ℝ f xStar with hgs
  have hexpand : ∀ p : E, g p - g (x t) =
      (g - gs) (p - x t) + gs (p - xStar) + gs (xStar - x t) := by
    intro p
    simp only [sub_apply, map_sub]
    ring
  have hsep : ∀ p ∈ F, ∀ q ∈ V, q ∉ F → g p < g q := by
    intro p hp q hq hqF
    have h1 := abs_lt.mp (hkey p (subset_convexHull ℝ _ (Finset.mem_coe.mpr (hFV hp))))
    have h2 := abs_lt.mp (hkey q (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq)))
    have h3 := hsc0 p hp
    have h4 := hsc1 q hq hqF
    have e1 := hexpand p
    have e2 := hexpand q
    linarith [h1.1, h1.2, h2.1, h2.2]
  -- the face is nonempty
  have hFne : F.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨w, hw0, hw1, hwx⟩ := (Finset.mem_convexHull').mp hxs.1
    have hsum : ∑ y ∈ V, w y * gs (y - xStar) = 0 := by
      have : ∑ y ∈ V, w y * gs (y - xStar) = gs (∑ y ∈ V, w y • y) - gs xStar := by
        simp only [map_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul,
          map_sum, map_smul, smul_eq_mul]
      rw [this, hwx, sub_self]
    have hge : ∑ y ∈ V, w y * κ ≤ ∑ y ∈ V, w y * gs (y - xStar) :=
      Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left
        (hsc1 y hy (by rw [hemp]; exact Finset.notMem_empty y)) (hw0 y hy))
    rw [← Finset.sum_mul, hw1, one_mul, hsum] at hge
    linarith
  obtain ⟨p₀, hp₀⟩ := hFne
  -- the atom is a convex combination of vertices that all minimize `g`, hence lie in `F`
  obtain ⟨hvC, hvmin, -, -⟩ := hrun.2 t
  obtain ⟨w, hw0, hw1, hwv⟩ := (Finset.mem_convexHull').mp hvC
  have hmin : ∀ y ∈ V, g (v t) ≤ g y := fun y hy =>
    hvmin y (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy))
  have hzero : ∑ y ∈ V, w y * (g y - g (v t)) = 0 := by
    have : ∑ y ∈ V, w y * (g y - g (v t)) = g (∑ y ∈ V, w y • y) - g (v t) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, map_sum,
        map_smul, smul_eq_mul]
    rw [this, hwv, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
    mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hmin y hy)))).mp hzero
  have hoff : ∀ q ∈ V \ F, w q = 0 := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    have hpos : 0 < g q - g (v t) := by
      have := hsep p₀ hp₀ q hq.1 hq.2
      have := hmin p₀ (hFV hp₀)
      linarith
    have := hterm q hq.1
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · linarith
  refine (Finset.mem_convexHull').mpr ⟨w, fun y hy => hw0 y (hFV hy), ?_, ?_⟩
  · rw [← Finset.sum_sdiff hFV, Finset.sum_eq_zero hoff, zero_add] at hw1; exact hw1
  · rw [← Finset.sum_sdiff hFV, Finset.sum_eq_zero (fun q hq => by rw [hoff q hq, zero_smul]),
      zero_add] at hwv
    exact hwv

set_option maxHeartbeats 1000000 in
/-- **Proposition 5.4.** -/
theorem polytope_gaps_bound {C Cs : Set E} {f : E → ℝ} {L B μ θ ρ : ℝ} {ℓ Q : ℕ} {x v : ℕ → E}
    (hCc : IsCompact C) (hC : Convex ℝ C) (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (hsm : IsSmoothOn C f L) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hB : ∀ y ∈ C, ‖fderiv ℝ f y‖ ≤ B) (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) (hCsc : IsCompact Cs) (hCs : Convex ℝ Cs)
    (hCsC : Cs ⊆ C) (hmin : minimizers C f ⊆ Cs) (hρ : 0 < ρ)
    (hball : ∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ Cs, ‖z - y‖ ≤ ρ → z ∈ Cs) (hℓ : 2 ≤ ℓ)
    (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t)) (hvCs : ∀ t, Q ≤ t → v t ∈ Cs)
    {m M : ℝ} (hmdef : m = ρ / (2 ^ (2 - θ) * μ))
    (hMdef : M = max (m / eta ℓ Q * (2 * Metric.diam C * B) ^ (1 - θ))
      (max ((L * Metric.diam C + B) * Metric.diam C / eta ℓ Q) (L * Metric.diam C ^ 2))) :
    IsStrongGrowth C f M 0 ∧
      IsRelaxedGapsGrowth C f x v (fun t => (eta ℓ t * M / m) ^ (1 / (1 - θ))) m θ Q := by
  have hxC : ∀ t, x t ∈ C := Lemmata.FrankWolfe.Proof.fw_run_mem C _ x v _ hC hrun
  set D := Metric.diam C with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (hxC 0))
  have hηQ : 0 < eta ℓ (Q : ℤ) := eta_nat_pos ℓ (by omega) Q
  have hm : 0 < m := by rw [hmdef]; positivity
  have hM1 : m / eta ℓ Q * (2 * D * B) ^ (1 - θ) ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hM2 : (L * D + B) * D / eta ℓ Q ≤ M := by
    rw [hMdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : L * D ^ 2 ≤ M := by rw [hMdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hM0 : 0 ≤ M := (by positivity : 0 ≤ L * D ^ 2).trans hM3
  refine ⟨?_, ?_⟩
  · have hsg := Proof.smooth_strong_growth C f L hC hCc.isBounded hL hsm
    intro y hy w hw hwmin η hη
    have h1 := hsg y hy w hw hwmin η hη
    rw [Real.rpow_zero, mul_one] at h1 ⊢
    have : 0 ≤ η ^ 2 / 2 := by positivity
    calc bregman f (y + η • (w - y)) y ≤ L * D ^ 2 * η ^ 2 / 2 := h1
      _ ≤ M * η ^ 2 / 2 := by nlinarith
  · intro t ht xStar hxs
    by_cases hlt : f (x t) - f xStar < (eta ℓ t * M / m) ^ (1 / (1 - θ))
    · exact Or.inl hlt
    right
    have hge := not_lt.mp hlt
    set h := f (x t) - f xStar with hh
    have hθ1 : θ < 1 := by linarith [hθ.2]
    have h1θ : 0 < 1 - θ := by linarith
    have hηt : 0 < eta ℓ (t : ℤ) := eta_nat_pos ℓ (by omega) t
    have hδ0 : 0 ≤ (eta ℓ t * M / m) ^ (1 / (1 - θ)) := by positivity
    have hh0 : 0 ≤ h := hδ0.trans hge
    have hxsCs : xStar ∈ Cs := hmin hxs
    have hminCs : minimizers Cs f = minimizers C f := by
      ext y
      constructor
      · intro hy
        exact ⟨hCsC hy.1, fun z hz => (hy.2 xStar hxsCs).trans (hxs.2 z hz)⟩
      · intro hy
        exact ⟨hmin hy, fun z hz => hy.2 z (hCsC hz)⟩
    have hebCs : IsHolderErrorBound Cs f μ θ := by
      intro y hy ys hys
      rw [hminCs] at hys ⊢
      exact heb y (hCsC hy) ys hys
    have hballCs : ∀ y ∈ minimizers Cs f, ∀ z ∈ affineSpan ℝ Cs, ‖z - y‖ ≤ ρ → z ∈ Cs := by
      rw [hminCs]; exact hball
    -- a nearest point of `C*` and the distance bound of Lemma 5.6
    obtain ⟨xb, hxb, hxbd⟩ := hCsc.exists_infDist_eq_dist ⟨xStar, hxsCs⟩ (x t)
    have hxbC := hCsC hxb
    set d := ‖x t - xb‖ with hd
    set a := eta ℓ (t : ℤ) / eta ℓ (Q : ℤ) with ha
    have hdist : d ≤ a ^ 2 * D := by
      have h1 := dist_active_bound hCs hℓ hrun hvCs t ht
      have h2 : Metric.infDist (x Q) Cs ≤ D :=
        (Metric.infDist_le_dist_of_mem hxsCs).trans
          (Metric.dist_le_diam_of_mem hCc.isBounded (hxC Q) (hCsC hxsCs))
      rw [hxbd, dist_eq_norm] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    -- Proposition 5.3 on the face at the nearest point
    obtain ⟨vb, hvb, hvbmin⟩ :=
      hCsc.exists_isMinOn ⟨xStar, hxsCs⟩ (fderiv ℝ f xb).continuous.continuousOn
    have hvbC := hCsC hvb
    have hgapb := interior_gap hCsc (hconv.subset hCsC hCs) (fun y hy => hdiff y (hCsC hy))
      hebCs hμ hθ1 hρ hballCs (by rw [hminCs]; exact hxs) hxb (fun y hy => hvbmin hy)
    -- comparing the gaps at `x_t` and at the nearest point
    obtain ⟨-, hvmin, -, -⟩ := hrun.2 t
    have hgt : fderiv ℝ f (x t) (x t - vb) ≤ fderiv ℝ f (x t) (x t - v t) := by
      have := hvmin vb hvbC
      rw [map_sub, map_sub]; linarith
    have hE1 : |fderiv ℝ f xb (x t - xb)| ≤ B * d := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ f xb (x t - xb)‖ ≤ ‖fderiv ℝ f xb‖ * ‖x t - xb‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * d := mul_le_mul_of_nonneg_right (hB xb hxbC) (norm_nonneg _)
    have hE2 : |(fderiv ℝ f (x t) - fderiv ℝ f xb) (x t - vb)| ≤ L * d * D := by
      rw [← Real.norm_eq_abs]
      have hvd : ‖x t - vb‖ ≤ D := by
        rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hCc.isBounded (hxC t) hvbC
      calc ‖(fderiv ℝ f (x t) - fderiv ℝ f xb) (x t - vb)‖ ≤
            ‖fderiv ℝ f (x t) - fderiv ℝ f xb‖ * ‖x t - vb‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * d * D := mul_le_mul (hlip _ (hxC t) _ hxbC) hvd (norm_nonneg _) (by positivity)
    have hE3 : |fderiv ℝ f (x t) (xb - x t)| ≤ B * d := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ f (x t) (xb - x t)‖ ≤ ‖fderiv ℝ f (x t)‖ * ‖xb - x t‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * d := by
            rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right (hB _ (hxC t)) (norm_nonneg _)
    have hsplit : fderiv ℝ f (x t) (x t - vb) = fderiv ℝ f xb (xb - vb) +
        fderiv ℝ f xb (x t - xb) + (fderiv ℝ f (x t) - fderiv ℝ f xb) (x t - vb) := by
      simp only [sub_apply, map_sub]; ring
    have hconvb : f (x t) + fderiv ℝ f (x t) (xb - x t) ≤ f xb :=
      Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv (hxC t) (hdiff _ (hxC t)) hxbC
    -- the constants
    have ha0 : 0 < a := div_pos hηt hηQ
    have ha1 : a ≤ 1 := by rw [ha, div_le_one hηQ]; exact eta_nat_anti ℓ (by omega) ht
    have hp2 : 1 / (1 - θ) ≤ 2 := by rw [div_le_iff₀ h1θ]; linarith [hθ.2]
    have ha2 : a ^ 2 ≤ a ^ (1 / (1 - θ)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge ha0 ha1 (by push_cast; exact hp2)
    have hδsplit : (eta ℓ t * M / m) ^ (1 / (1 - θ)) =
        a ^ (1 / (1 - θ)) * (eta ℓ Q * M / m) ^ (1 / (1 - θ)) := by
      rw [← Real.mul_rpow ha0.le (by positivity)]
      congr 1
      rw [ha]; field_simp
    have hbig : 2 * D * B ≤ (eta ℓ Q * M / m) ^ (1 / (1 - θ)) := by
      have h1 : (2 * D * B) ^ (1 - θ) ≤ eta ℓ Q * M / m := by
        rw [le_div_iff₀ hm]
        have := hM1
        rw [div_mul_eq_mul_div, div_le_iff₀ hηQ] at this
        linarith
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ 1 / (1 - θ))
      rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel h1θ.ne', Real.rpow_one] at h2
    have hBd : B * d ≤ h / 2 := by
      have hapos : 0 ≤ a ^ (1 / (1 - θ)) := by positivity
      calc B * d ≤ B * (a ^ 2 * D) := mul_le_mul_of_nonneg_left hdist hB0
        _ ≤ B * (a ^ (1 / (1 - θ)) * D) := by gcongr
        _ = (2 * D * B) * a ^ (1 / (1 - θ)) / 2 := by ring
        _ ≤ (eta ℓ Q * M / m) ^ (1 / (1 - θ)) * a ^ (1 / (1 - θ)) / 2 := by gcongr
        _ = (eta ℓ t * M / m) ^ (1 / (1 - θ)) / 2 := by rw [hδsplit]; ring
        _ ≤ h / 2 := by linarith
    have hBLd : (B + L * D) * d ≤ M * eta ℓ t := by
      have h1 : d ≤ a * D := hdist.trans (mul_le_mul_of_nonneg_right (by nlinarith) hD0)
      have h2 : (L * D + B) * D ≤ M * eta ℓ Q := by
        have := hM2; rwa [div_le_iff₀ hηQ] at this
      calc (B + L * D) * d ≤ (B + L * D) * (a * D) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (L * D + B) * D * a := by ring
        _ ≤ M * eta ℓ Q * a := mul_le_mul_of_nonneg_right h2 ha0.le
        _ = M * eta ℓ t := by rw [ha]; field_simp
    have hfb : h / 2 ≤ f xb - f xStar := by
      have := (abs_le.mp hE3).1
      linarith
    have hpow : (h / 2) ^ (1 - θ) ≤ (f xb - f xStar) ^ (1 - θ) :=
      Real.rpow_le_rpow (by linarith) hfb h1θ.le
    have h2m : ρ / μ * (h / 2) ^ (1 - θ) = 2 * m * h ^ (1 - θ) := by
      rw [hmdef, Real.div_rpow hh0 (by norm_num : (0 : ℝ) ≤ 2)]
      have e : (2 : ℝ) ^ (2 - θ) = 2 * 2 ^ (1 - θ) := by
        rw [show (2 : ℝ) - θ = 1 + (1 - θ) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
      rw [e]
      field_simp
    have hmh : M * eta ℓ t ≤ m * h ^ (1 - θ) := by
      have h1 := Real.rpow_le_rpow hδ0 hge h1θ.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1θ.ne', Real.rpow_one,
        div_le_iff₀ hm] at h1
      linarith
    have hρμ : 0 ≤ ρ / μ := by positivity
    calc m * h ^ (1 - θ) = 2 * m * h ^ (1 - θ) - m * h ^ (1 - θ) := by ring
      _ ≤ ρ / μ * (f xb - f xStar) ^ (1 - θ) - M * eta ℓ t := by
          have := mul_le_mul_of_nonneg_left hpow hρμ
          linarith
      _ ≤ fderiv ℝ f xb (xb - vb) - (B + L * D) * d := by linarith
      _ ≤ fderiv ℝ f (x t) (x t - vb) := by
          rw [hsplit]
          have := (abs_le.mp hE1).1
          have := (abs_le.mp hE2).1
          linarith
      _ ≤ fderiv ℝ f (x t) (x t - v t) := hgt

/-- **Corollary 5.5.** -/
theorem polytope_rate_bound {C Cs : Set E} {f : E → ℝ} {L B μ θ ρ : ℝ} {ℓ Q : ℕ} {x v : ℕ → E}
    {xStar : E} (hCc : IsCompact C) (hC : Convex ℝ C) (hconv : ConvexOn ℝ C f)
    (hdiff : ∀ y ∈ C, DifferentiableAt ℝ f y) (hsm : IsSmoothOn C f L) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hB : ∀ y ∈ C, ‖fderiv ℝ f y‖ ≤ B) (hD : 0 < Metric.diam C)
    (heb : IsHolderErrorBound C f μ θ) (hμ : 0 < μ) (hθ : θ ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hCsc : IsCompact Cs) (hCs : Convex ℝ Cs) (hCsC : Cs ⊆ C) (hmin : minimizers C f ⊆ Cs)
    (hρ : 0 < ρ) (hball : ∀ y ∈ minimizers C f, ∀ z ∈ affineSpan ℝ Cs, ‖z - y‖ ≤ ρ → z ∈ Cs)
    (hℓ : 2 ≤ ℓ) (hrun : IsFWRun C (fderiv ℝ f) x v (fun t => eta ℓ t))
    (hvCs : ∀ t, Q ≤ t → v t ∈ Cs) (hxs : xStar ∈ minimizers C f)
    {m M : ℝ} (hmdef : m = ρ / (2 ^ (2 - θ) * μ))
    (hMdef : M = max (m / eta ℓ Q * (2 * Metric.diam C * B) ^ (1 - θ))
      (max ((L * Metric.diam C + B) * Metric.diam C / eta ℓ Q) (L * Metric.diam C ^ 2)))
    {S : ℕ} (hSdef : S = max (max 1 ⌈(2 : ℝ) ^ (1 / θ) * ℓ * M / m ^ (1 / θ) - ℓ⌉₊) Q) :
    ∀ t : ℕ, S ≤ t → f (x t) - f xStar ≤
      max ((f (x S) - f xStar) * (eta ℓ ((t : ℤ) - 1) / eta ℓ ((S : ℤ) - 1)) ^ ℓ)
        (eta ℓ ((t : ℤ) - 1) ^ (min (ℓ : ℝ) (min (1 / (1 - θ)) 2)) *
          ((M / m) ^ (1 / (1 - θ)) + M / 2)) := by
  obtain ⟨hg, hrel⟩ := polytope_gaps_bound hCc hC hconv hdiff hsm hL.le hlip hB heb hμ
    ⟨hθ.1.le, hθ.2⟩ hCsc hCs hCsC hmin hρ hball hℓ hrun hvCs hmdef hMdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hM : 0 < M := lt_of_lt_of_le (by positivity : 0 < L * Metric.diam C ^ 2)
    (by rw [hMdef]; exact (le_max_right _ _).trans (le_max_right _ _))
  have hrelS : IsRelaxedGapsGrowth C f x v (fun t => (eta ℓ t * M / m) ^ (1 / (1 - θ))) m θ S :=
    fun t ht xs hxs' => hrel t (le_trans (by rw [hSdef]; exact le_max_right _ _) ht) xs hxs'
  exact relaxed_gaps_bound hconv hdiff hxs hM hm hℓ ⟨hθ.1, by linarith [hθ.2]⟩ hg hrun
    (by rw [hSdef]; exact le_max_left _ _) hrelS

namespace Proof

theorem distance_to_active_set : DistanceToActiveSet.{u} := by
  intro E _ _ C K f' ℓ Q x v hK hℓ hrun hvK t ht
  exact dist_active_bound hK hℓ hrun hvK t ht

theorem open_loop_active_set : OpenLoopActiveSet.{u} := by
  intro E _ _ V F f L μ θ κ ℓ x v xStar hFV hconv hdiff hsm hL hlip hdiam huniq heb hμ hθ hκ
    hsc1 hsc0 hℓ hrun t ht
  exact active_set_ell hFV hconv hdiff hsm hL hlip hdiam huniq heb hμ hθ hκ hsc1 hsc0 hℓ hrun t ht

theorem polytope_relaxed_gaps : PolytopeRelaxedGaps.{u} := by
  intro E _ _ C Cs f L B μ θ ρ ℓ Q x v hCc hC hconv hdiff hsm hL hlip hB heb hμ hθ hCsc hCs
    hCsC hmin hρ hball hℓ hrun hvCs
  exact polytope_gaps_bound hCc hC hconv hdiff hsm hL hlip hB heb hμ hθ hCsc hCs hCsC hmin hρ
    hball hℓ hrun hvCs rfl rfl

theorem polytope_rate : PolytopeRate.{u} := by
  intro E _ _ C Cs f L B μ θ ρ ℓ Q x v xStar hCc hC hconv hdiff hsm hL hlip hB hD heb hμ hθ
    hCsc hCs hCsC hmin hρ hball hℓ hrun hvCs hxs
  exact polytope_rate_bound hCc hC hconv hdiff hsm hL hlip hB hD heb hμ hθ hCsc hCs hCsC hmin
    hρ hball hℓ hrun hvCs hxs rfl rfl rfl

end Proof

end Lemmata.FWAffineOpenLoop
