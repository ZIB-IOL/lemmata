module

public import Lemmata.FWUniformlyConvex.Local
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

/-!
# Online linear optimization over uniformly convex sets (Section 3)

Lemma 3.2 follows from the scaling inequality of uniformly convex sets at both maximizers. The
regret of follow the leader is `∑_{t ≤ T} t ⟨∇F_t, x_t - x_{t+1}⟩` for the averages `∇F_t` of the
losses, and Lemma 3.2 bounds each term by `2M (2M/(α L))^{1/(q-1)} t^{-1/(q-1)}`, since consecutive
averages differ by at most `2M/t`.
-/

namespace Lemmata.FWUniformlyConvex

open Lemmata.FrankWolfe Lemmata.CGBasics

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 3.2.** -/
theorem maximizer_stability_bound {C : Set E} {α q : ℝ} {φ₁ φ₂ : StrongDual ℝ E} {v₁ v₂ : E}
    (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q) (hmax : 0 < max ‖φ₁‖ ‖φ₂‖)
    (hv₁ : v₁ ∈ C) (h₁ : ∀ y ∈ C, φ₁ y ≤ φ₁ v₁) (hv₂ : v₂ ∈ C) (h₂ : ∀ y ∈ C, φ₂ y ≤ φ₂ v₂) :
    φ₁ (v₁ - v₂) ≤ (1 / α) ^ (1 / (q - 1)) * ‖φ₁ - φ₂‖ ^ (1 + 1 / (q - 1)) /
      (max ‖φ₁‖ ‖φ₂‖) ^ (1 / (q - 1)) := by
  set m := max ‖φ₁‖ ‖φ₂‖ with hm
  set X := ‖φ₁ - φ₂‖ with hX
  set d := ‖v₁ - v₂‖ with hd
  have hq1 : 0 < q - 1 := by linarith
  have hs1 := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α q hUC (-φ₁) v₁ hv₁
    (fun y hy => by simp only [neg_apply]; linarith [h₁ y hy]) v₂ hv₂
  have hs2 := Lemmata.CGBasics.Proof.uniformly_convex_scaling C α q hUC (-φ₂) v₂ hv₂
    (fun y hy => by simp only [neg_apply]; linarith [h₂ y hy]) v₁ hv₁
  rw [norm_neg, norm_sub_rev, neg_apply, ← map_neg, neg_sub] at hs1
  rw [norm_neg, neg_apply, ← map_neg, neg_sub] at hs2
  have hp1 : 0 ≤ φ₁ (v₁ - v₂) := by rw [map_sub]; linarith [h₁ v₂ hv₂]
  have hp2 : 0 ≤ φ₂ (v₂ - v₁) := by rw [map_sub]; linarith [h₂ v₁ hv₁]
  have hsplit : (φ₁ - φ₂) (v₁ - v₂) = φ₁ (v₁ - v₂) + φ₂ (v₂ - v₁) := by
    simp only [sub_apply, map_sub]; ring
  have hcs : (φ₁ - φ₂) (v₁ - v₂) ≤ X * d :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
  have hdq : 0 ≤ d ^ q := Real.rpow_nonneg (norm_nonneg _) q
  have hmd : α * m * d ^ q ≤ X * d := by
    rcases le_total ‖φ₁‖ ‖φ₂‖ with hle | hle
    · rw [hm, max_eq_right hle]; linarith
    · rw [hm, max_eq_left hle]; linarith
  have hRHS : 0 ≤ (1 / α) ^ (1 / (q - 1)) * X ^ (1 + 1 / (q - 1)) / m ^ (1 / (q - 1)) := by
    positivity
  rcases eq_or_lt_of_le (norm_nonneg (v₁ - v₂)) with hd0 | hdpos
  · have : v₁ - v₂ = 0 := norm_eq_zero.mp hd0.symm
    rw [this, map_zero]; exact hRHS
  have hd' : 0 < d := hdpos
  -- `α m d^{q-1} ≤ X`
  have hdq1 : d ^ q = d ^ (q - 1) * d := by
    rw [← Real.rpow_add_one hd'.ne']; congr 1; ring
  have hk : α * m * d ^ (q - 1) ≤ X := by
    rw [hdq1] at hmd
    have := le_of_mul_le_mul_right (by linarith : α * m * d ^ (q - 1) * d ≤ X * d) hd'
    exact this
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hk
  -- `d ≤ (X/(α m))^{1/(q-1)}`
  have hdle : d ≤ (X / (α * m)) ^ (1 / (q - 1)) := by
    have h1 : d ^ (q - 1) ≤ X / (α * m) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ 1 / (q - 1))
    rwa [← Real.rpow_mul hd'.le, mul_one_div_cancel hq1.ne', Real.rpow_one] at h2
  calc φ₁ (v₁ - v₂) ≤ (φ₁ - φ₂) (v₁ - v₂) := by rw [hsplit]; linarith
    _ ≤ X * d := hcs
    _ ≤ X * (X / (α * m)) ^ (1 / (q - 1)) := mul_le_mul_of_nonneg_left hdle hXpos.le
    _ = (1 / α) ^ (1 / (q - 1)) * X ^ (1 + 1 / (q - 1)) / m ^ (1 / (q - 1)) := by
        rw [Real.rpow_add hXpos, Real.rpow_one, Real.div_rpow hXpos.le (by positivity),
          Real.mul_rpow hα.le hmax.le, Real.div_rpow zero_le_one hα.le, Real.one_rpow]
        field_simp

/-- The averages of the losses. -/
noncomputable def avg (c : ℕ → StrongDual ℝ E) (t : ℕ) : StrongDual ℝ E :=
  (1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, c τ

theorem sum_Icc_eq (c : ℕ → StrongDual ℝ E) (t : ℕ) :
    ∑ τ ∈ Finset.Icc 1 t, c τ = (t : ℝ) • avg c t := by
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0; simp
  · rw [avg, smul_smul, mul_one_div_cancel (by exact_mod_cast hpos.ne'), one_smul]

theorem avg_norm_le {c : ℕ → StrongDual ℝ E} {M : ℝ} (hM : ∀ t, ‖c t‖ ≤ M) (t : ℕ) :
    ‖avg c t‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0; simp [avg, hM0]
  have htpos : (0 : ℝ) < t := by exact_mod_cast hpos
  rw [avg, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ τ ∈ Finset.Icc 1 t, c τ‖ ≤ t * M := by
    calc ‖∑ τ ∈ Finset.Icc 1 t, c τ‖ ≤ ∑ τ ∈ Finset.Icc 1 t, ‖c τ‖ := norm_sum_le _ _
      _ ≤ ∑ _τ ∈ Finset.Icc 1 t, M := Finset.sum_le_sum (fun τ _ => hM τ)
      _ = t * M := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  rw [one_div, inv_mul_le_iff₀ htpos]
  exact h1

theorem avg_step {c : ℕ → StrongDual ℝ E} {M : ℝ} (hM : ∀ t, ‖c t‖ ≤ M) {t : ℕ} (ht : 1 ≤ t) :
    ‖avg c t - avg c (t - 1)‖ ≤ 2 * M / t := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hS : ∑ τ ∈ Finset.Icc 1 t, c τ = ∑ τ ∈ Finset.Icc 1 (t - 1), c τ + c t := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
  have hid : avg c t - avg c (t - 1) = (1 / (t : ℝ)) • (c t - avg c (t - 1)) := by
    have e1 := sum_Icc_eq c t
    have e2 := sum_Icc_eq c (t - 1)
    have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub ht]; push_cast; ring
    rw [hS, e2, hcast] at e1
    -- `(t - 1) • a_{t-1} + c_t = t • a_t`
    have key : (t : ℝ) • (avg c t - avg c (t - 1)) = c t - avg c (t - 1) := by
      rw [smul_sub, ← e1]; module
    rw [← key, smul_smul, one_div_mul_cancel htpos.ne', one_smul]
  rw [hid, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖c t - avg c (t - 1)‖ ≤ 2 * M := by
    calc ‖c t - avg c (t - 1)‖ ≤ ‖c t‖ + ‖avg c (t - 1)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM t) (avg_norm_le hM _)
      _ = 2 * M := by ring
  calc 1 / (t : ℝ) * ‖c t - avg c (t - 1)‖ ≤ 1 / t * (2 * M) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * M / t := by ring

/-- The regret identity of follow the leader (Huang et al., Proposition 2), as an inequality
against every comparator. -/
theorem ftl_regret_le {C : Set E} {c : ℕ → StrongDual ℝ E} {x : ℕ → E} (hftl : IsFTL C c x)
    {u : E} (hu : u ∈ C) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, c t (x t - u) ≤
      ∑ t ∈ Finset.Icc 1 T, (∑ τ ∈ Finset.Icc 1 t, c τ) (x t - x (t + 1)) := by
  set S : ℕ → StrongDual ℝ E := fun t => ∑ τ ∈ Finset.Icc 1 t, c τ with hSdef
  have hIco : ∀ t, ∑ τ ∈ Finset.Ico 1 (t + 1), c τ = S t := fun t => by
    rw [hSdef]; simp only
    congr 1
  have hmin : ∀ t, ∀ y ∈ C, S t (x (t + 1)) ≤ S t y := fun t y hy => by
    have := (hftl (t + 1) (by omega)).2 y hy
    rwa [hIco t] at this
  -- the identity `∑ c_t(x_t) - S_T(x_{T+1}) = ∑ S_t(x_t - x_{t+1})`
  have hid : ∀ T : ℕ, ∑ t ∈ Finset.Icc 1 T, c t (x t) - S T (x (T + 1)) =
      ∑ t ∈ Finset.Icc 1 T, S t (x t - x (t + 1)) := by
    intro T
    induction T with
    | zero => simp [hSdef]
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← ih]
      have hS1 : S (T + 1) = S T + c (T + 1) := by
        rw [hSdef]; simp only; rw [Finset.sum_Icc_succ_top (by omega)]
      rw [hS1]
      simp only [add_apply, map_sub]
      ring
  have hsum : ∑ t ∈ Finset.Icc 1 T, c t (x t - u) =
      ∑ t ∈ Finset.Icc 1 T, c t (x t) - S T u := by
    simp only [map_sub, Finset.sum_sub_distrib, hSdef, FunLike.coe_sum,
      Finset.sum_apply]
  rw [hsum, ← hid T]
  linarith [hmin T u hu]

/-- Each term of the regret is at most `2M (2M/(α L))^{1/(q-1)} t^{-1/(q-1)}`. -/
theorem ftl_term_bound {C : Set E} {α q M L : ℝ} {c : ℕ → StrongDual ℝ E} {x : ℕ → E}
    (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q) (hL : 0 < L)
    (hM : ∀ t, ‖c t‖ ≤ M) (hftl : IsFTL C c x) {t : ℕ} (ht : 1 ≤ t) (havg : L ≤ ‖avg c t‖) :
    (∑ τ ∈ Finset.Icc 1 t, c τ) (x t - x (t + 1)) ≤
      2 * M * (2 * M / (α * L)) ^ (1 / (q - 1)) * (t : ℝ) ^ (-(1 / (q - 1))) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hMpos : 0 < M := lt_of_lt_of_le hL (havg.trans (avg_norm_le hM t))
  set p := 1 / (q - 1) with hp
  have hq1 : 0 < q - 1 := by linarith
  have hp0 : 0 < p := by positivity
  -- minimality of `x_{t+1}` for `avg t` and of `x_t` for `avg (t - 1)`
  have hIco : ∀ s : ℕ, ∑ τ ∈ Finset.Ico 1 (s + 1), c τ = (s : ℝ) • avg c s := by
    intro s
    rw [← sum_Icc_eq c s]
    congr 1
  have hmin1 : ∀ y ∈ C, avg c t (x (t + 1)) ≤ avg c t y := by
    intro y hy
    have h := (hftl (t + 1) (by omega)).2 y hy
    rw [hIco t, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul] at h
    exact le_of_mul_le_mul_left h htpos
  have hmin2 : ∀ y ∈ C, avg c (t - 1) (x t) ≤ avg c (t - 1) y := by
    intro y hy
    rcases Nat.eq_or_lt_of_le ht with h1 | h1
    · subst h1; simp [avg]
    have h := (hftl t ht).2 y hy
    have ht' : t = (t - 1) + 1 := by omega
    rw [ht', hIco (t - 1), ← ht', smul_apply, smul_apply,
      smul_eq_mul, smul_eq_mul] at h
    have : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < t - 1)
    exact le_of_mul_le_mul_left h this
  have hmax : 0 < max ‖-avg c t‖ ‖-avg c (t - 1)‖ :=
    lt_of_lt_of_le hL (by rw [norm_neg]; exact havg.trans (le_max_left _ _))
  have hstab := maximizer_stability_bound hUC hα hq hmax (hftl (t + 1) (by omega)).1
    (fun y hy => by simp only [neg_apply]; linarith [hmin1 y hy]) (hftl t ht).1
    (fun y hy => by simp only [neg_apply]; linarith [hmin2 y hy])
  rw [norm_neg, norm_neg, neg_sub_neg, neg_apply, ← map_neg, neg_sub] at hstab
  -- `‖avg t - avg (t-1)‖ ≤ 2M/t` and `max ≥ L`
  set A := 2 * M / t with hA
  have hApos : 0 < A := by positivity
  have hstep := avg_step hM ht
  rw [norm_sub_rev] at hstab
  have hb : avg c t (x t - x (t + 1)) ≤ (1 / α) ^ p * A ^ (1 + p) / L ^ p := by
    refine hstab.trans ?_
    have h1 : ‖avg c t - avg c (t - 1)‖ ^ (1 + p) ≤ A ^ (1 + p) :=
      Real.rpow_le_rpow (norm_nonneg _) hstep (by positivity)
    have h2 : L ^ p ≤ (max ‖avg c t‖ ‖avg c (t - 1)‖) ^ p :=
      Real.rpow_le_rpow hL.le (havg.trans (le_max_left _ _)) hp0.le
    have hLp : 0 < L ^ p := by positivity
    calc (1 / α) ^ p * ‖avg c t - avg c (t - 1)‖ ^ (1 + p) /
          (max ‖avg c t‖ ‖avg c (t - 1)‖) ^ p ≤
        (1 / α) ^ p * ‖avg c t - avg c (t - 1)‖ ^ (1 + p) / L ^ p := by
          apply div_le_div_of_nonneg_left (by positivity) hLp h2
      _ ≤ (1 / α) ^ p * A ^ (1 + p) / L ^ p := by gcongr
  have e1 : (1 / α) ^ p * A ^ (1 + p) / L ^ p = A * (A / (α * L)) ^ p := by
    rw [Real.rpow_add hApos, Real.rpow_one, Real.div_rpow hApos.le (by positivity),
      Real.mul_rpow hα.le hL.le, Real.div_rpow zero_le_one hα.le, Real.one_rpow]
    field_simp
  have e2 : (A / (α * L)) ^ p = (2 * M / (α * L)) ^ p * (t : ℝ) ^ (-p) := by
    rw [show A / (α * L) = (2 * M / (α * L)) * (t : ℝ)⁻¹ by rw [hA]; field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow htpos.le,
      Real.rpow_neg htpos.le]
  rw [sum_Icc_eq c t, smul_apply, smul_eq_mul]
  calc (t : ℝ) * avg c t (x t - x (t + 1)) ≤ t * (A * (A / (α * L)) ^ p) := by
        rw [← e1]; exact mul_le_mul_of_nonneg_left hb htpos.le
    _ = 2 * M * (2 * M / (α * L)) ^ p * (t : ℝ) ^ (-p) := by
        rw [e2, hA]; field_simp

/-- `∑_{t=1}^T t^{-p} ≤ T^{1-p}/(1-p)` for `0 < p < 1`. -/
theorem sum_rpow_neg_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ^ (-p) ≤ (T : ℝ) ^ (1 - p) / (1 - p) := by
  have h1p : 0 < 1 - p := by linarith
  rcases Nat.eq_zero_or_pos T with h0 | hT
  · subst h0
    simp only [Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty, Nat.cast_zero]
    exact div_nonneg (Real.rpow_nonneg le_rfl _) h1p.le
  -- split off `t = 1`
  have hshift : ∀ T : ℕ, 1 ≤ T → ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ^ (-p) =
      1 + ∑ i ∈ Finset.Ico 1 T, ((i + 1 : ℕ) : ℝ) ^ (-p) := by
    intro T hT
    induction T, hT using Nat.le_induction with
    | base => simp
    | succ T hT ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Ico_succ_top hT]
      ring
  rw [hshift T hT]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc (1 : ℕ) T) := by
    intro a ha b hb hab
    simp only [Set.mem_Icc, Nat.cast_one] at ha hb
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have hint := hanti.sum_le_integral_Ico hT
  rw [integral_rpow (Or.inl (by linarith))] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  have e : -p + 1 = 1 - p := by ring
  rw [e] at hint
  have hsum : ∑ i ∈ Finset.Ico 1 T, ((i + 1 : ℕ) : ℝ) ^ (-p) ≤
      ((T : ℝ) ^ (1 - p) - 1) / (1 - p) := by
    convert hint using 2
  have : 1 ≤ 1 / (1 - p) := by rw [le_div_iff₀ h1p]; linarith
  have hfin : 1 + ((T : ℝ) ^ (1 - p) - 1) / (1 - p) ≤ (T : ℝ) ^ (1 - p) / (1 - p) := by
    rw [sub_div]
    have : 1 ≤ 1 / (1 - p) := this
    linarith
  linarith

/-- `∑_{t=1}^T 1/t ≤ 1 + log T`. -/
theorem sum_inv_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ^ (-(1 : ℝ)) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa [Real.rpow_neg_one] using h

/-- **Theorem 3.1.** -/
theorem ftl_regret_bound {C : Set E} {α q M L : ℝ} {c : ℕ → StrongDual ℝ E} {x : ℕ → E} {T : ℕ}
    (hUC : IsUniformlyConvexSet C α q) (hα : 0 < α) (hq : 2 ≤ q) (hL : 0 < L)
    (hM : ∀ t, ‖c t‖ ≤ M) (havg : ∀ t, 1 ≤ t → t ≤ T → L ≤ ‖avg c t‖) (hftl : IsFTL C c x)
    {u : E} (hu : u ∈ C) :
    ∑ t ∈ Finset.Icc 1 T, c t (x t - u) ≤
      2 * M * (2 * M / (α * L)) ^ (1 / (q - 1)) *
        ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ^ (-(1 / (q - 1))) := by
  rw [Finset.mul_sum]
  refine (ftl_regret_le hftl hu T).trans (Finset.sum_le_sum (fun t ht => ?_))
  obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
  exact ftl_term_bound hUC hα hq hL hM hftl ht1 (havg t ht1 htT)

namespace Proof

theorem maximizer_stability : MaximizerStability.{u} := by
  intro E _ _ C α q φ₁ φ₂ v₁ v₂ hUC hα hq hmax hv₁ h₁ hv₂ h₂
  exact maximizer_stability_bound hUC hα hq hmax hv₁ h₁ hv₂ h₂

theorem ftl_regret : FTLRegret.{u} := by
  intro E _ _ C α q M L c x T hUC hα hq hL hM havg hftl u hu
  have hb := ftl_regret_bound (T := T) hUC hα hq hL hM havg hftl hu
  have hMpos : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hq1 : 0 < q - 1 := by linarith
  have hc0 : 0 ≤ 2 * M * (2 * M / (α * L)) ^ (1 / (q - 1)) := by positivity
  refine ⟨fun hq2 => ?_, fun hq2 => ?_⟩
  · have hp1 : 1 / (q - 1) < 1 := by rw [div_lt_one hq1]; linarith
    have hs := sum_rpow_neg_le (by positivity) hp1 T
    have e : (T : ℝ) ^ (1 - 1 / (q - 1)) / (1 - 1 / (q - 1)) =
        (q - 1) / (q - 2) * (T : ℝ) ^ (1 - 1 / (q - 1)) := by
      have h1 : 1 / (1 - 1 / (q - 1)) = (q - 1) / (q - 2) := by
        have e1 : 1 - 1 / (q - 1) = (q - 2) / (q - 1) := by field_simp; ring
        rw [e1, one_div_div]
      rw [div_eq_mul_one_div, h1, mul_comm]
    rw [e] at hs
    calc _ ≤ _ := hb
      _ ≤ 2 * M * (2 * M / (α * L)) ^ (1 / (q - 1)) *
          ((q - 1) / (q - 2) * (T : ℝ) ^ (1 - 1 / (q - 1))) := mul_le_mul_of_nonneg_left hs hc0
      _ = _ := by ring
  · subst hq2
    have e : (1 : ℝ) / (2 - 1) = 1 := by norm_num
    rw [e, Real.rpow_one] at hb
    have hs := sum_inv_le T
    calc _ ≤ _ := hb
      _ ≤ 2 * M * (2 * M / (α * L)) * (1 + Real.log T) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 4 * M ^ 2 / (α * L) * (1 + Real.log T) := by ring

end Proof

end Lemmata.FWUniformlyConvex
