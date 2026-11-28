module

public import Lemmata.FWRestart.Wolfe
public import Lemmata.BPCG.Main

@[expose] public section

/-!
# Fractional away-step Frank–Wolfe

Each step of Algorithm 1 that is not a drop step moves along a direction `d` with
`-f'(x)(d) > G = e^{-γ} w₀/2`; by exact line search (which, stopped before `η_max`, minimizes along
the whole ray by convexity) and smoothness it decreases `f` by at least `η G - η² L D²/2` for every
`η ∈ [0, 1]`. Drop steps decrease the size of the active set by one, and every other step increases
it by at most one. A potential argument then bounds the number of iterations by
`|S₀| - |S_T| + 2 (f(x₀) - f(x_T))/P` for every lower bound `P` of the progress of the full steps
(Proposition 4.1). In the burn-in regime `G > L D²` the full steps make progress `G/2`, and chaining
runs gives Proposition 4.2.
-/

namespace Lemmata.FWRestart

open Lemmata.FrankWolfe Lemmata.CGBasics Lemmata.AwayStepFW Lemmata.AwayStepFW.Proof

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact line search on `[0, η_max]` that stops before `η_max` minimizes along the whole ray. -/
theorem ls_extend {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x u : E} {η ηmax s : ℝ}
    (hη : η < ηmax) (hη0 : 0 ≤ η)
    (hmin : ∀ s ∈ Set.Icc (0 : ℝ) ηmax, f (x - η • u) ≤ f (x - s • u))
    (hs : 0 ≤ s) : f (x - η • u) ≤ f (x - s • u) := by
  rcases le_or_gt s ηmax with hle | hlt
  · exact hmin s ⟨hs, hle⟩
  · set a := (s - ηmax) / (s - η) with ha
    set b := (ηmax - η) / (s - η) with hb
    have hsη : 0 < s - η := by linarith
    have ha0 : 0 ≤ a := div_nonneg (by linarith) hsη.le
    have hb0 : 0 < b := div_pos (by linarith) hsη
    have hab : a + b = 1 := by rw [ha, hb, ← add_div]; field_simp; ring
    have hcomb : a * η + b * s = ηmax := by rw [ha, hb]; field_simp; ring
    have hpt : a • (x - η • u) + b • (x - s • u) = x - ηmax • u := by
      have : a • (x - η • u) + b • (x - s • u) = (a + b) • x - (a * η + b * s) • u := by
        simp only [smul_sub, add_smul, mul_smul]; abel
      rw [this, hab, hcomb, one_smul]
    have hconv := hf.2 (Set.mem_univ (x - η • u)) (Set.mem_univ (x - s • u)) ha0 hb0.le hab
    rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
    have h1 := hmin ηmax ⟨by linarith, le_rfl⟩
    have e : a * f (x - η • u) + b * f (x - η • u) = f (x - η • u) := by
      rw [← add_mul, hab, one_mul]
    have key : b * f (x - η • u) ≤ b * f (x - s • u) := by linarith
    exact le_of_mul_le_mul_left key hb0

open Classical in
/-- The away update with any step `η ∈ [0, λ_a/(1 - λ_a)]` keeps the invariant. -/
theorem inv_away_update {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) {a : E} (ha : a ∈ S) (hlt : lam a < 1) {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) (lam a / (1 - lam a))) :
    Inv V (x - η • (a - x)) (if η = lam a / (1 - lam a) then S.erase a else S)
      (fun w => (1 + η) * lam w - if w = a then η else 0) := by
  set γmax := lam a / (1 - lam a) with hγmax
  have hnna : 0 ≤ (1 + η) * lam a - η := by
    have : η * (1 - lam a) ≤ lam a := by
      rw [← le_div_iff₀ (by linarith)]; exact hη.2
    nlinarith
  have hsumS : ∑ w ∈ S, ((1 + η) * lam w - if w = a then η else 0) = 1 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h.sum, Finset.sum_ite_eq', ite_eq_left ha]; ring
  have hrepS : ∑ w ∈ S, ((1 + η) * lam w - if w = a then η else 0) • w = x - η • (a - x) := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← h.rep, ite_smul,
      zero_smul, Finset.sum_ite_eq', ite_eq_left ha]
    module
  rcases eq_or_ne η γmax with hd | hd
  · rw [ite_eq_left hd]
    have hza : (1 + η) * lam a - η = 0 := by
      rw [hd, hγmax]; field_simp; ring
    refine ⟨(Finset.erase_subset a S).trans h.sub, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
    · by_cases hwa : w = a
      · simp only [hwa, ite_true]; exact hnna
      · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith [hη.1]) (h.nonneg w)
    · by_cases hwa : w = a
      · simp only [hwa, ite_true]; exact hza
      · have hwS : w ∉ S := fun hwS => hw (Finset.mem_erase.mpr ⟨hwa, hwS⟩)
        simp [hwa, h.supp w hwS]
    · rw [Finset.sum_erase _ (by simp only [ite_true]; exact hza)]; exact hsumS
    · rw [Finset.sum_erase _ (by simp only [ite_true]; rw [hza, zero_smul])]; exact hrepS.symm
  · rw [ite_eq_right hd]
    refine ⟨h.sub, fun w => ?_, fun w hw => ?_, hsumS, hrepS.symm⟩
    · by_cases hwa : w = a
      · simp only [hwa, ite_true]; exact hnna
      · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith [hη.1]) (h.nonneg w)
    · have hwa : w ≠ a := fun e => hw (e ▸ ha)
      simp [hwa, h.supp w hw]

theorem inv_of_weighted {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : IsWeightedState V x S lam) : Inv V x S lam :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem mem_hull_of_inv {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) : x ∈ convexHull ℝ (↑V : Set E) :=
  convexHull_mono (by exact_mod_cast h.sub) h.mem_convexHull

/-- The strong Wolfe gap does not depend on the choice of the vertices. -/
theorem gap_eq {g : StrongDual ℝ E} {V S : Finset E} {v v' a a' : E} (hv : v ∈ V) (hv' : v' ∈ V)
    (hvV : ∀ y ∈ V, g v ≤ g y) (hv'V : ∀ y ∈ V, g v' ≤ g y) (ha : a ∈ S) (ha' : a' ∈ S)
    (haS : ∀ y ∈ S, g y ≤ g a) (ha'S : ∀ y ∈ S, g y ≤ g a') : g (a - v) = g (a' - v') := by
  have := hvV v' hv'
  have := hv'V v hv
  have := haS a' ha'
  have := ha'S a ha
  rw [map_sub, map_sub]
  linarith

/-- The strong Wolfe gap bounds the primal gap (the first part of Lemma 2.3, for nonnegative
weights). -/
theorem primal_le_gap {V : Finset E} {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam)
    {v a : E} (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w)
    (haS : ∀ w ∈ S, fderiv ℝ f x w ≤ fderiv ℝ f x a) {y : E}
    (hy : y ∈ convexHull ℝ (↑V : Set E)) : f x - f y ≤ fderiv ℝ f x (a - v) := by
  have hc := Lemmata.FrankWolfe.convexOn_add_fderiv_le hconv (Set.mem_univ x) (hdiff x)
    (Set.mem_univ y)
  have h1 := Proof.le_of_min_vertex (fderiv ℝ f x) hv hy
  have h2 := h.apply_le (fderiv ℝ f x) haS
  rw [map_sub] at hc ⊢
  linarith

theorem gap_nonneg {V : Finset E} {g : StrongDual ℝ E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) {v a : E} (hv : ∀ w ∈ V, g v ≤ g w) (haS : ∀ w ∈ S, g w ≤ g a) :
    0 ≤ g (a - v) := by
  have h1 := h.le_apply g hv
  have h2 := h.apply_le g haS
  rw [map_sub]
  linarith

/-- The quadratic curvature bound of an `L`-smooth function over a set of diameter at most `D`. -/
theorem smooth_curv {V : Finset E} {f : E → ℝ} {L : NNReal} {D : ℝ} (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D) :
    ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
      ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + η ^ 2 * (L * D ^ 2) / 2 := by
  intro x _ u hu v hv η hη
  have h1 := Lemmata.FrankWolfe.descent_lemma f L hsm x (x + η • (u - v))
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hη.1] at h1
  have h3 : (η * ‖u - v‖) ^ 2 ≤ η ^ 2 * D ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hD u hu v hv) 2)
      (sq_nonneg η)
  have h4 : (L : ℝ) / 2 * (η * ‖u - v‖) ^ 2 ≤ (L : ℝ) / 2 * (η ^ 2 * D ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith

/-- The outcome of one step of Algorithm 1 before stopping, for a curvature bound `φ`: the
invariant is kept, `f` does not increase, and either the step is a drop step (the active set shrinks
by one) or the active set grows by at most one and `f` decreases by `η G - φ(η)` for every
`η ∈ [0, 1]`. -/
theorem fafw_step_outcome_gen {V : Finset E} {f : E → ℝ} {φ : ℝ → ℝ} {G : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hcurv : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
      ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + φ η)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {v a : E}
    (hvV : v ∈ V) (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (hgap : 2 * G < fderiv ℝ f x (a - v))
    {x' : E} {S' : Finset E} {lam' : E → ℝ} (hstep : IsFAFWStep f G x S lam v a x' S' lam') :
    Inv V x' S' lam' ∧ f x' ≤ f x ∧
      ((S'.card ≤ S.card + 1 ∧ ∀ η ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f x - η * G + φ η) ∨
        S'.card + 1 = S.card) := by
  classical
  set g := fderiv ℝ f x with hg
  have hxC : x ∈ convexHull ℝ (↑V : Set E) := mem_hull_of_inv h
  have hvC : v ∈ convexHull ℝ (↑V : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hvV)
  have haC : a ∈ convexHull ℝ (↑V : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (h.sub ha))
  have hdesc : ∀ p ∈ convexHull ℝ (↑V : Set E), ∀ q ∈ convexHull ℝ (↑V : Set E),
      G < g (q - p) → ∀ s ∈ Set.Icc (0 : ℝ) 1, f (x - s • (q - p)) ≤ f x - s * G + φ s := by
    intro p hp q hq hGu s hs
    have h1 := hcurv x hxC p hp q hq s hs
    have e : x + s • (p - q) = x - s • (q - p) := by
      rw [← neg_sub q p, smul_neg, ← sub_eq_add_neg]
    have e2 : g (p - q) = -g (q - p) := by rw [← map_neg, neg_sub]
    rw [e, e2] at h1
    have h2 : s * G ≤ s * g (q - p) := mul_le_mul_of_nonneg_left hGu.le hs.1
    linarith
  unfold IsFAFWStep at hstep
  split_ifs at hstep with hfw
  · obtain ⟨η, hη, hmin, hx', hlam', hS'⟩ := hstep
    have hinv := Lemmata.BPCG.Proof.inv_fw_step h hvV hη
    rw [← hx', ← hlam', ← hS'] at hinv
    refine ⟨hinv, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [hx']
      have := hmin 0 ⟨le_rfl, zero_le_one⟩
      simpa using this
    · rw [hS']
      split_ifs
      · simp
      · exact Finset.card_insert_le v S
    · intro s hs
      rw [hx']
      exact (hmin s hs).trans (hdesc v hvC x hxC hfw s hs)
  · push Not at hfw
    obtain ⟨η, hη, hmin, hx', hlam', hS'⟩ := hstep
    have hGa : G < g (a - x) := by
      rw [map_sub] at hgap hfw ⊢
      linarith
    have hnot : ¬ g (a - x) ≤ g (x - v) := fun hle => by linarith
    have hlt := h.lam_lt_one g hv ha hnot
    have hinv := inv_away_update h ha hlt hη
    rw [← hx', ← hlam', ← hS'] at hinv
    refine ⟨hinv, ?_, ?_⟩
    · rw [hx']
      have := hmin 0 ⟨le_rfl, div_nonneg (h.nonneg a) (by linarith)⟩
      simpa using this
    · rcases eq_or_ne η (lam a / (1 - lam a)) with hd | hd
      · right
        rw [hS', ite_eq_left hd]
        exact Finset.card_erase_add_one ha
      · left
        refine ⟨by rw [hS', ite_eq_right hd]; omega, fun s hs => ?_⟩
        have hηlt : η < lam a / (1 - lam a) := lt_of_le_of_ne hη.2 hd
        rw [hx']
        exact (ls_extend hconv hηlt hη.1 hmin hs.1).trans (hdesc x hxC a haC hGa s hs)

/-- The outcome of one step of Algorithm 1 before stopping, for an `L`-smooth `f`. -/
theorem fafw_step_outcome {V : Finset E} {f : E → ℝ} {L : NNReal} {D G : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam) {v a : E}
    (hvV : v ∈ V) (hv : ∀ w ∈ V, fderiv ℝ f x v ≤ fderiv ℝ f x w) (ha : a ∈ S)
    (hgap : 2 * G < fderiv ℝ f x (a - v))
    {x' : E} {S' : Finset E} {lam' : E → ℝ} (hstep : IsFAFWStep f G x S lam v a x' S' lam') :
    Inv V x' S' lam' ∧ f x' ≤ f x ∧
      ((S'.card ≤ S.card + 1 ∧
          ∀ η ∈ Set.Icc (0 : ℝ) 1, f x' ≤ f x - η * G + η ^ 2 * (L * D ^ 2) / 2) ∨
        S'.card + 1 = S.card) :=
  fafw_step_outcome_gen hconv (smooth_curv hsm hD) h hvV hv ha hgap hstep

/-- The potential bound over `n` consecutive iterations of Algorithm 1 with stopping level `ε`,
for a curvature bound `φ` and a lower bound `P > 0` of the progress `η₀ ε/2 - φ(η₀)` of the full
steps. -/
theorem segment_bound_gen {V : Finset E} {f : E → ℝ} {φ : ℝ → ℝ} {ε P η₀ : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hcurv : ∀ x ∈ convexHull ℝ (↑V : Set E), ∀ u ∈ convexHull ℝ (↑V : Set E),
      ∀ v ∈ convexHull ℝ (↑V : Set E), ∀ η ∈ Set.Icc (0 : ℝ) 1,
        f (x + η • (u - v)) ≤ f x + η * fderiv ℝ f x (u - v) + φ η)
    (hη₀ : η₀ ∈ Set.Icc (0 : ℝ) 1) (hP : 0 < P) (hPle : P ≤ η₀ * (ε / 2) - φ η₀)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀)) :
    ∀ n : ℕ, (∀ i < n, IsFAFWIter V f ε x S lam (t₀ + i)) →
      Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
        (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card + 2 * (f (x t₀) - f (x (t₀ + n))) / P := by
  intro n
  induction n with
  | zero => intro _; simp [h0]
  | succ n ih =>
    intro hit
    obtain ⟨hinv, hb⟩ := ih (fun i hi => hit i (by omega))
    obtain ⟨v, hvV, hv, a, ha, -, hgap, hstep⟩ := hit n (by omega)
    have hgap' : 2 * (ε / 2) < fderiv ℝ f (x (t₀ + n)) (a - v) := by linarith
    obtain ⟨hinv', hdec, hcase⟩ := fafw_step_outcome_gen hconv hcurv hinv hvV hv ha hgap' hstep
    rw [show t₀ + (n + 1) = t₀ + n + 1 by omega]
    refine ⟨hinv', ?_⟩
    have hsplit : 2 * (f (x t₀) - f (x (t₀ + n + 1))) / P =
        2 * (f (x t₀) - f (x (t₀ + n))) / P + 2 * (f (x (t₀ + n)) - f (x (t₀ + n + 1))) / P := by
      field_simp; ring
    rw [hsplit]
    push_cast
    rcases hcase with ⟨hcard, hprog⟩ | hcard
    · have hP' : P ≤ f (x (t₀ + n)) - f (x (t₀ + n + 1)) := by
        have := hprog η₀ hη₀
        linarith
      have h2 : 2 ≤ 2 * (f (x (t₀ + n)) - f (x (t₀ + n + 1))) / P := by
        rw [le_div_iff₀ hP]; linarith
      have hc : ((S (t₀ + n + 1)).card : ℝ) ≤ (S (t₀ + n)).card + 1 := by exact_mod_cast hcard
      linarith
    · have h2 : 0 ≤ 2 * (f (x (t₀ + n)) - f (x (t₀ + n + 1))) / P :=
        div_nonneg (by linarith) hP.le
      have hc : ((S (t₀ + n + 1)).card : ℝ) + 1 = (S (t₀ + n)).card := by exact_mod_cast hcard
      linarith

/-- The potential bound over `n` consecutive iterations of Algorithm 1 for an `L`-smooth `f`. -/
theorem segment_bound {V : Finset E} {f : E → ℝ} {L : NNReal} {D ε P η₀ : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    (hη₀ : η₀ ∈ Set.Icc (0 : ℝ) 1) (hP : 0 < P)
    (hPle : P ≤ η₀ * (ε / 2) - η₀ ^ 2 * (L * D ^ 2) / 2)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀)) :
    ∀ n : ℕ, (∀ i < n, IsFAFWIter V f ε x S lam (t₀ + i)) →
      Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
        (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card + 2 * (f (x t₀) - f (x (t₀ + n))) / P :=
  segment_bound_gen hconv (smooth_curv hsm hD) hη₀ hP hPle h0

/-- The algebra of Proposition 4.1: `2 μ w₀^r/P = 16 e^{2γ} C μ w₀^{r-2}` for
`P = (e^{-γ} w₀/2)²/(2C)`. -/
theorem complexity_algebra {γ w₀ μ r C : ℝ} (hw₀ : 0 < w₀) (hC : 0 < C) :
    2 * (μ * w₀ ^ r) / ((Real.exp (-γ) * w₀ / 2) ^ 2 / (2 * C)) =
      16 * Real.exp (2 * γ) * C * μ * w₀ ^ (r - 2) := by
  have he : Real.exp (2 * γ) * Real.exp (-γ) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hepos : 0 < Real.exp (-γ) := Real.exp_pos _
  have hE : Real.exp (2 * γ) = 1 / Real.exp (-γ) ^ 2 := by
    rw [eq_div_iff (by positivity)]; exact he
  rw [Real.rpow_sub hw₀, Real.rpow_two, hE]
  field_simp
  ring

namespace Proof

/-- Proposition 4.1 for a run of Algorithm 1 started at iteration `t₀`. -/
theorem regular_run {V : Finset E} {f : E → ℝ} {L : NNReal} {D γ w₀ μ r : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    (hw₀ : 0 < w₀) (hburn : Real.exp (-γ) * w₀ / 2 ≤ L * D ^ 2)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀))
    (hprimal : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x t₀) - f y ≤ μ * w₀ ^ r) (n : ℕ)
    (hit : ∀ i < n, IsFAFWIter V f (Real.exp (-γ) * w₀) x S lam (t₀ + i)) :
    Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
      (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card +
        16 * Real.exp (2 * γ) * (L * D ^ 2) * μ * w₀ ^ (r - 2) := by
  set ε := Real.exp (-γ) * w₀ with hε
  set C := (L : ℝ) * D ^ 2 with hC
  have hεpos : 0 < ε := mul_pos (Real.exp_pos _) hw₀
  have hCpos : 0 < C := by linarith
  have hη₀ : ε / 2 / C ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by positivity) hCpos.le, (div_le_one hCpos).mpr hburn⟩
  have hP : 0 < (ε / 2) ^ 2 / (2 * C) := by positivity
  have hPle : (ε / 2) ^ 2 / (2 * C) ≤ ε / 2 / C * (ε / 2) - (ε / 2 / C) ^ 2 * C / 2 := by
    rw [show ε / 2 / C * (ε / 2) - (ε / 2 / C) ^ 2 * C / 2 = (ε / 2) ^ 2 / (2 * C) by
      field_simp; ring]
  obtain ⟨hinvT, hbound⟩ := segment_bound hconv hsm hD hη₀ hP hPle h0 n hit
  refine ⟨hinvT, ?_⟩
  have hfT := hprimal (x (t₀ + n)) (mem_hull_of_inv hinvT)
  have hstep : 2 * (f (x t₀) - f (x (t₀ + n))) / ((ε / 2) ^ 2 / (2 * C)) ≤
      2 * (μ * w₀ ^ r) / ((ε / 2) ^ 2 / (2 * C)) :=
    div_le_div_of_nonneg_right (by linarith) hP.le
  rw [hε, complexity_algebra hw₀ hCpos] at hstep
  linarith

theorem fractional_complexity : FractionalComplexity.{u} := by
  intro E _ _ V f L D γ w₀ μ r x S lam T hconv hsm hD hw₀ hburn hrun hprimal
  obtain ⟨hst, hit⟩ := hrun
  have h := (regular_run hconv hsm hD hw₀ hburn (t₀ := 0) (by simpa using inv_of_weighted hst)
    (by simpa using hprimal) T (fun i hi => by simpa using hit i hi)).2
  simpa using h

/-- The number of iterations of one run of Algorithm 1 in the burn-in regime
`e^{-γ} w₀/2 ≥ L D²`: at most `|S_{t₀}| - |S_{t₀+n}| + 8 e^γ`. -/
theorem burn_in_run {V : Finset E} {f : E → ℝ} {L : NNReal} {D γ w₀ : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hsm : IsSmooth f L)
    (hD : ∀ y ∈ convexHull ℝ (↑V : Set E), ∀ z ∈ convexHull ℝ (↑V : Set E), ‖y - z‖ ≤ D)
    (hw₀ : 0 < w₀) (hlarge : L * D ^ 2 ≤ Real.exp (-γ) * w₀ / 2)
    {x : ℕ → E} {S : ℕ → Finset E} {lam : ℕ → E → ℝ} {t₀ : ℕ}
    (h0 : Inv V (x t₀) (S t₀) (lam t₀))
    (hprimal : ∀ y ∈ convexHull ℝ (↑V : Set E), f (x t₀) - f y ≤ w₀) (n : ℕ)
    (hit : ∀ i < n, IsFAFWIter V f (Real.exp (-γ) * w₀) x S lam (t₀ + i)) :
    Inv V (x (t₀ + n)) (S (t₀ + n)) (lam (t₀ + n)) ∧
      (n : ℝ) ≤ (S t₀).card - (S (t₀ + n)).card + 8 * Real.exp γ := by
  set ε := Real.exp (-γ) * w₀ with hε
  have hεpos : 0 < ε := mul_pos (Real.exp_pos _) hw₀
  have hP : 0 < ε / 4 := by positivity
  have hPle : ε / 4 ≤ 1 * (ε / 2) - 1 ^ 2 * (L * D ^ 2) / 2 := by linarith
  obtain ⟨hinv, hb⟩ := segment_bound hconv hsm hD ⟨zero_le_one, le_rfl⟩ hP hPle h0 n hit
  refine ⟨hinv, ?_⟩
  have hf := hprimal (x (t₀ + n)) (mem_hull_of_inv hinv)
  have h1 : 2 * (f (x t₀) - f (x (t₀ + n))) / (ε / 4) ≤ 2 * w₀ / (ε / 4) :=
    div_le_div_of_nonneg_right (by linarith) hP.le
  have h2 : 2 * w₀ / (ε / 4) = 8 * Real.exp γ := by
    rw [hε, Real.exp_neg]
    field_simp
    norm_num
  linarith

end Proof

end Lemmata.FWRestart
