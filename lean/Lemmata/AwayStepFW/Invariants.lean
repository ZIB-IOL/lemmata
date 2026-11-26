module

public import Lemmata.AwayStepFW.Defs
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# Invariants of away-step Frank–Wolfe

Along a run, the active set lies in `V`, the weights are nonnegative, vanish outside the active set,
sum to `1`, and represent the iterate. Hence the iterate lies in the convex hull of its active set.
-/

namespace Lemmata.AwayStepFW

namespace Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The invariant of the state `(x, S, λ)` of away-step Frank–Wolfe on `conv V`. -/
structure Inv (V : Finset E) (x : E) (S : Finset E) (lam : E → ℝ) : Prop where
  sub : S ⊆ V
  nonneg : ∀ w, 0 ≤ lam w
  supp : ∀ w ∉ S, lam w = 0
  sum : ∑ w ∈ S, lam w = 1
  rep : x = ∑ w ∈ S, lam w • w

theorem Inv.mem_convexHull {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ}
    (h : Inv V x S lam) : x ∈ convexHull ℝ (↑S : Set E) := by
  rw [h.rep]
  exact (convex_convexHull ℝ _).sum_mem (fun w _ => h.nonneg w) h.sum
    (fun w hw => subset_convexHull ℝ _ hw)

theorem Inv.apply_le {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam)
    (g : StrongDual ℝ E) {a : E} (ha : ∀ w ∈ S, g w ≤ g a) : g x ≤ g a := by
  rw [h.rep, map_sum]
  calc ∑ w ∈ S, g (lam w • w) = ∑ w ∈ S, lam w * g w := by simp [map_smul, smul_eq_mul]
    _ ≤ ∑ w ∈ S, lam w * g a :=
        Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (ha w hw) (h.nonneg w))
    _ = g a := by rw [← Finset.sum_mul, h.sum, one_mul]

theorem Inv.le_apply {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam)
    (g : StrongDual ℝ E) {v : E} (hv : ∀ w ∈ V, g v ≤ g w) : g v ≤ g x := by
  rw [h.rep, map_sum]
  calc g v = ∑ w ∈ S, lam w * g v := by rw [← Finset.sum_mul, h.sum, one_mul]
    _ ≤ ∑ w ∈ S, lam w * g w :=
        Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (hv w (h.sub hw)) (h.nonneg w))
    _ = ∑ w ∈ S, g (lam w • w) := by simp [map_smul, smul_eq_mul]

/-- The weight of an away vertex is below `1` when the away step is taken. -/
theorem Inv.lam_lt_one {V : Finset E} {x : E} {S : Finset E} {lam : E → ℝ} (h : Inv V x S lam)
    (g : StrongDual ℝ E) {v a : E} (hv : ∀ w ∈ V, g v ≤ g w) (ha : a ∈ S)
    (hnot : ¬ g (a - x) ≤ g (x - v)) : lam a < 1 := by
  classical
  have hle : lam a ≤ 1 := by
    rw [← h.sum]
    exact Finset.single_le_sum (fun w _ => h.nonneg w) ha
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply hnot
    have hzero : ∀ w ∈ S, w ≠ a → lam w = 0 := by
      intro w hw hwa
      have := Finset.sum_erase_add S lam ha
      rw [h.sum, heq] at this
      have hs : ∑ w ∈ S.erase a, lam w = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => h.nonneg w)).mp hs w
        (Finset.mem_erase.mpr ⟨hwa, hw⟩)
    have hx : x = a := by
      rw [h.rep, ← Finset.sum_erase_add S _ ha, heq, one_smul]
      rw [Finset.sum_eq_zero (fun w hw => by
        rw [hzero w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw), zero_smul]), zero_add]
    rw [hx, sub_self, map_zero, map_sub]
    linarith [hv a (h.sub ha)]

theorem Inv.step {V : Finset E} {L : ℝ} (hL : 0 ≤ L) {g : StrongDual ℝ E} {x : E} {S : Finset E}
    {lam : E → ℝ} (h : Inv V x S lam) {v a : E} (hvV : v ∈ V) (hv : ∀ w ∈ V, g v ≤ g w)
    (ha : a ∈ S) (haS : ∀ w ∈ S, g w ≤ g a) {x' : E} {S' : Finset E} {lam' : E → ℝ}
    (hstep : IsAFWStep L g x S lam v a x' S' lam') : Inv V x' S' lam' := by
  classical
  unfold IsAFWStep at hstep
  split_ifs at hstep with hfw
  · dsimp only at hstep
    obtain ⟨hx', hlam', hS'⟩ := hstep
    set γ := min (g (x - v) / (L * ‖x - v‖ ^ 2)) 1 with hγ
    have hg0 : 0 ≤ g (x - v) := by rw [map_sub]; linarith [h.le_apply g hv]
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hg0 (by positivity)) zero_le_one
    have hγ1 : γ ≤ 1 := min_le_right _ _
    have hsub : S ⊆ insert v S := Finset.subset_insert v S
    have hsumlam : ∑ w ∈ insert v S, lam w = 1 := by
      rw [← h.sum]; symm
      exact Finset.sum_subset hsub (fun w _ hw => h.supp w hw)
    have hsumx : ∑ w ∈ insert v S, lam w • w = x := by
      rw [h.rep]; symm
      exact Finset.sum_subset hsub (fun w _ hw => by rw [h.supp w hw, zero_smul])
    subst hlam'
    rcases eq_or_ne γ 1 with h1 | h1
    · rw [ite_eq_left h1] at hS'
      subst hS'
      refine ⟨by simpa using hvV, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · have := h.nonneg w; split_ifs <;> nlinarith
      · rw [Finset.mem_singleton] at hw; simp [hw, h1]
      · simp [h1]
      · rw [hx', h1]; simp
    · rw [ite_eq_right h1] at hS'
      subst hS'
      refine ⟨Finset.insert_subset hvV h.sub, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · have := h.nonneg w; split_ifs <;> nlinarith
      · rw [Finset.mem_insert, not_or] at hw
        simp [hw.1, h.supp w hw.2]
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumlam, Finset.sum_ite_eq']
        simp
      · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hsumx, ite_smul,
          zero_smul, Finset.sum_ite_eq', Finset.mem_insert_self, ite_true]
        rw [hx']
        module
  · dsimp only at hstep
    obtain ⟨hx', hlam', hS'⟩ := hstep
    have hlt := h.lam_lt_one g hv ha hfw
    set γmax := lam a / (1 - lam a) with hγmax
    set γ := min (g (a - x) / (L * ‖a - x‖ ^ 2)) γmax with hγ
    have hga : 0 ≤ g (a - x) := by rw [map_sub]; linarith [h.apply_le g haS]
    have hmax0 : 0 ≤ γmax := div_nonneg (h.nonneg a) (by linarith)
    have hγ0 : 0 ≤ γ := le_min (div_nonneg hga (by positivity)) hmax0
    have hγle : γ ≤ γmax := min_le_right _ _
    have hnna : 0 ≤ (1 + γ) * lam a - γ := by
      have : γ * (1 - lam a) ≤ lam a := by
        rw [← le_div_iff₀ (by linarith)]; exact hγle
      nlinarith
    have hsumS : ∑ w ∈ S, ((1 + γ) * lam w - if w = a then γ else 0) = 1 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h.sum, Finset.sum_ite_eq', ite_eq_left ha]; ring
    have hrepS : ∑ w ∈ S, ((1 + γ) * lam w - if w = a then γ else 0) • w = x' := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← h.rep, ite_smul,
        zero_smul, Finset.sum_ite_eq', ite_eq_left ha]
      rw [hx']
      module
    subst hlam'
    rcases eq_or_ne γ γmax with hd | hd
    · rw [ite_eq_left hd] at hS'
      subst hS'
      have hza : (1 + γ) * lam a - γ = 0 := by
        rw [hd, hγmax]; field_simp; ring
      refine ⟨(Finset.erase_subset a S).trans h.sub, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hnna
        · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith) (h.nonneg w)
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hza
        · have hwS : w ∉ S := fun hwS => hw (Finset.mem_erase.mpr ⟨hwa, hwS⟩)
          simp [hwa, h.supp w hwS]
      · rw [Finset.sum_erase _ (by simp only [ite_true]; exact hza)]; exact hsumS
      · rw [Finset.sum_erase _ (by simp only [ite_true]; rw [hza, zero_smul])]; exact hrepS.symm
    · rw [ite_eq_right hd] at hS'
      subst hS'
      refine ⟨h.sub, fun w => ?_, fun w hw => ?_, hsumS, hrepS.symm⟩
      · by_cases hwa : w = a
        · simp only [hwa, ite_true]; exact hnna
        · simp only [hwa, ite_false, sub_zero]; exact mul_nonneg (by linarith) (h.nonneg w)
      · have hwa : w ≠ a := fun e => hw (e ▸ ha)
        simp [hwa, h.supp w hw]

theorem run_inv {V : Finset E} {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L) {x : ℕ → E} {S : ℕ → Finset E}
    {lam : ℕ → E → ℝ} (h : IsAFWRun V f L x S lam) : ∀ t, Inv V (x t) (S t) (lam t) := by
  classical
  obtain ⟨hx0, hS0, hlam0, hsteps⟩ := h
  intro t
  induction t with
  | zero =>
    refine ⟨by rw [hS0]; simpa using hx0, fun w => ?_, fun w hw => ?_, ?_, ?_⟩
    · rw [hlam0]; dsimp only; split_ifs <;> norm_num
    · rw [hS0, Finset.mem_singleton] at hw; rw [hlam0]; simp [hw]
    · rw [hS0, hlam0]; simp
    · rw [hS0, hlam0]; simp
  | succ t ih =>
    obtain ⟨v, hvV, hv, a, ha, haS, hstep⟩ := hsteps t
    exact ih.step hL hvV hv ha haS hstep

end Proof

end Lemmata.AwayStepFW
