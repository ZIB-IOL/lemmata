module

public import Lemmata.FanoDiffusion.Entropy

@[expose] public section

/-!
# Independent samples (Corollary 2.4)

For samples `Y = (Y_1, …, Y_n)` that are i.i.d. given `X`, with `Q` the product of the laws of the
`Y_i`, the "golden formula" `Σ_x P(x) D(P_x ‖ Q) = I(X; Y) + D(P_Y ‖ Q)` and Gibbs' inequality give
`I(X; Y) ≤ Σ_x P(x) D(P_x ‖ Q) = n I(X; Y_1)`. Convexity of the logarithm bounds `I(X; Y_1)` by the
largest relative entropy between the conditional laws.
-/

namespace Lemmata.FanoDiffusion

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

universe u

namespace Proof

section RealSums

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The law of one coordinate of a product law. -/
theorem sum_prod_mul_coord {n : ℕ} (q : β → ℝ) (hq : ∑ c, q c = 1) (j : Fin n) (g : β → ℝ) :
    ∑ y : Fin n → β, (∏ i, q (y i)) * g (y j) = ∑ c, q c * g c := by
  classical
  have h1 : ∀ y : Fin n → β, (∏ i, q (y i)) * g (y j) =
      ∏ i, (q (y i) * if i = j then g (y i) else 1) := by
    intro y
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq' j (fun i => g (y i))]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i c => q c * if i = j then g c else 1)]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [hij, hq]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sum_prod_eq_one {n : ℕ} (q : β → ℝ) (hq : ∑ c, q c = 1) :
    ∑ y : Fin n → β, ∏ i, q (y i) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun _ c => q c)]
  simp [hq]

/-- Gibbs' inequality for finite sums. -/
theorem gibbs_sum {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hP0 : ∀ i, 0 ≤ P i) (hQ0 : ∀ i, 0 ≤ Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i ≤ 1) (hac : ∀ i, 0 < P i → 0 < Q i) :
    0 ≤ ∑ i, P i * log (P i / Q i) := by
  have h : ∀ i, P i * log (Q i / P i) ≤ Q i - P i := by
    intro i
    rcases eq_or_lt_of_le (hP0 i) with h0 | hpos
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact hQ0 i
    · have hq := hac i hpos
      have h2 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq hpos)) hpos.le
      rw [mul_sub, mul_div_cancel₀ _ hpos.ne', mul_one] at h2
      exact h2
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_sub_distrib, hP1] at hsum
  have h3 : ∀ i, P i * log (P i / Q i) = -(P i * log (Q i / P i)) := by
    intro i
    rw [show Q i / P i = (P i / Q i)⁻¹ from (inv_div _ _).symm, log_inv]
    ring
  simp_rw [h3]
  rw [Finset.sum_neg_distrib]
  linarith

/-- Jensen's inequality for the logarithm. -/
theorem log_mix_ge {ι : Type*} [Fintype ι] (w a : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (ha : ∀ i, 0 < a i) :
    ∑ i, w i * log (a i) ≤ log (∑ i, w i * a i) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ) (w := w) (p := a)
    (fun i _ => hw0 i) hw1 (fun i _ => ha i)
  simpa [smul_eq_mul] using h

end RealSums

section Samples

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `I(X; Y) ≤ n I(X; Y_1)` for samples that are i.i.d. given `X`, in terms of the point masses. -/
theorem samples_mi_le {n : ℕ} (p : α → ℝ) (q : α → β → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (hq0 : ∀ x c, 0 ≤ q x c) (hq1 : ∀ x, ∑ c, q x c = 1) :
    ∑ z : α × (Fin n → β), p z.1 * (∏ i, q z.1 (z.2 i)) *
        log (p z.1 * (∏ i, q z.1 (z.2 i)) / (p z.1 * ∑ x', p x' * ∏ i, q x' (z.2 i))) ≤
      n * ∑ z : α × β, p z.1 * q z.1 z.2 *
        log (p z.1 * q z.1 z.2 / (p z.1 * ∑ x', p x' * q x' z.2)) := by
  classical
  obtain ⟨Px, hPx⟩ : ∃ f : α → (Fin n → β) → ℝ, ∀ x y, f x y = ∏ i, q x (y i) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨PY, hPY⟩ : ∃ f : (Fin n → β) → ℝ, ∀ y, f y = ∑ x', p x' * Px x' y := ⟨_, fun _ => rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ f : β → ℝ, ∀ c, f c = ∑ x', p x' * q x' c := ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ f : (Fin n → β) → ℝ, ∀ y, f y = ∏ i, P1 (y i) := ⟨_, fun _ => rfl⟩
  simp_rw [← hPx, ← hPY, ← hP1]
  have hPx0 : ∀ x y, 0 ≤ Px x y := fun x y => by
    rw [hPx]
    exact Finset.prod_nonneg fun i _ => hq0 x (y i)
  have hPY0 : ∀ y, 0 ≤ PY y := fun y => by
    rw [hPY]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hPx0 x y)
  have hP10 : ∀ c, 0 ≤ P1 c := fun c => by
    rw [hP1]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hq0 x c)
  have hQ0 : ∀ y, 0 ≤ Q y := fun y => by
    rw [hQ]
    exact Finset.prod_nonneg fun i _ => hP10 (y i)
  have hPpos : ∀ x y, 0 < p x * Px x y → 0 < PY y ∧ 0 < Q y ∧ 0 < Px x y ∧ 0 < p x ∧
      ∀ i, 0 < q x (y i) ∧ 0 < P1 (y i) := by
    intro x y h
    have hpx : 0 < p x := lt_of_le_of_ne (hp0 x) (fun h0 => by rw [← h0, zero_mul] at h; linarith)
    have hPxy : 0 < Px x y :=
      lt_of_le_of_ne (hPx0 x y) (fun h0 => by rw [← h0, mul_zero] at h; linarith)
    have hqi : ∀ i, 0 < q x (y i) := fun i => by
      have hne : Px x y ≠ 0 := hPxy.ne'
      rw [hPx, Finset.prod_ne_zero_iff] at hne
      exact lt_of_le_of_ne (hq0 x (y i)) (Ne.symm (hne i (Finset.mem_univ i)))
    have hP1i : ∀ i, 0 < P1 (y i) := fun i => by
      rw [hP1]
      exact lt_of_lt_of_le (mul_pos hpx (hqi i))
        (Finset.single_le_sum (f := fun x' => p x' * q x' (y i))
          (fun x' _ => mul_nonneg (hp0 x') (hq0 x' (y i))) (Finset.mem_univ x))
    have hPYy : 0 < PY y := by
      rw [hPY]
      exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun x' => p x' * Px x' y)
        (fun x' _ => mul_nonneg (hp0 x') (hPx0 x' y)) (Finset.mem_univ x))
    have hQy : 0 < Q y := by
      rw [hQ]
      exact Finset.prod_pos fun i _ => hP1i i
    exact ⟨hPYy, hQy, hPxy, hpx, fun i => ⟨hqi i, hP1i i⟩⟩
  -- split every term of the left-hand side
  have hA : ∀ z : α × (Fin n → β),
      p z.1 * Px z.1 z.2 * log (p z.1 * Px z.1 z.2 / (p z.1 * PY z.2)) =
        p z.1 * Px z.1 z.2 * log (Px z.1 z.2 / Q z.2) -
          p z.1 * Px z.1 z.2 * log (PY z.2 / Q z.2) := by
    rintro ⟨x, y⟩
    rcases eq_or_lt_of_le (mul_nonneg (hp0 x) (hPx0 x y)) with h | h
    · simp only
      rw [← h]
      ring
    · obtain ⟨hPYy, hQy, hPxy, hpx, -⟩ := hPpos x y h
      simp only
      rw [mul_div_mul_left _ _ hpx.ne', log_div hPxy.ne' hPYy.ne', log_div hPxy.ne' hQy.ne',
        log_div hPYy.ne' hQy.ne']
      ring
  rw [Finset.sum_congr rfl fun z _ => hA z, Finset.sum_sub_distrib]
  -- the first part is `n I(X; Y_1)`
  have hB : ∑ z : α × (Fin n → β), p z.1 * Px z.1 z.2 * log (Px z.1 z.2 / Q z.2) =
      n * ∑ z : α × β, p z.1 * q z.1 z.2 * log (p z.1 * q z.1 z.2 / (p z.1 * P1 z.2)) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only
    rcases eq_or_lt_of_le (hp0 x) with h0 | hpx
    · rw [← h0]
      simp
    · -- inner sums
      have hR : ∑ c, p x * q x c * log (p x * q x c / (p x * P1 c)) =
          p x * ∑ c, q x c * log (q x c / P1 c) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_div_mul_left _ _ hpx.ne']
        ring
      have hL : ∀ y, Px x y * log (Px x y / Q y) =
          Px x y * ∑ j, log (q x (y j) / P1 (y j)) := by
        intro y
        rcases eq_or_lt_of_le (hPx0 x y) with h | h
        · rw [← h]
          ring
        · obtain ⟨-, hQy, -, -, hi⟩ := hPpos x y (mul_pos hpx h)
          congr 1
          rw [log_div h.ne' hQy.ne', hPx, hQ, log_prod (fun i _ => (hi i).1.ne'),
            log_prod (fun i _ => (hi i).2.ne'), ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => (log_div (hi j).1.ne' (hi j).2.ne').symm
      have hsum : ∑ y, Px x y * ∑ j, log (q x (y j) / P1 (y j)) =
          n * ∑ c, q x c * log (q x c / P1 c) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hc : ∀ j : Fin n, ∑ y : Fin n → β, Px x y * log (q x (y j) / P1 (y j)) =
            ∑ c, q x c * log (q x c / P1 c) := fun j => by
          simp_rw [hPx]
          exact sum_prod_mul_coord (q x) (hq1 x) j (fun c => log (q x c / P1 c))
        rw [Finset.sum_congr rfl fun j _ => hc j, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      rw [hR]
      calc ∑ y, p x * Px x y * log (Px x y / Q y) = p x * ∑ y, Px x y * log (Px x y / Q y) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
        _ = p x * (n * ∑ c, q x c * log (q x c / P1 c)) := by
            rw [Finset.sum_congr rfl fun y _ => hL y, hsum]
        _ = n * (p x * ∑ c, q x c * log (q x c / P1 c)) := by ring
  -- the second part is a relative entropy
  have hC : 0 ≤ ∑ z : α × (Fin n → β), p z.1 * Px z.1 z.2 * log (PY z.2 / Q z.2) := by
    have e : ∑ z : α × (Fin n → β), p z.1 * Px z.1 z.2 * log (PY z.2 / Q z.2) =
        ∑ y, PY y * log (PY y / Q y) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only
      rw [← Finset.sum_mul, ← hPY y]
    rw [e]
    have hPY1 : ∑ y, PY y = 1 := by
      simp_rw [hPY]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hPx, sum_prod_eq_one (q _) (hq1 _), mul_one]
      exact hp1
    have hP11 : ∑ c, P1 c = 1 := by
      simp_rw [hP1]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hq1, mul_one]
      exact hp1
    have hQ1 : ∑ y, Q y ≤ 1 := by
      simp_rw [hQ]
      rw [sum_prod_eq_one P1 hP11]
    refine gibbs_sum PY Q hPY0 hQ0 hPY1 hQ1 fun y hy => ?_
    rw [hPY] at hy
    obtain ⟨x, -, hx⟩ := Finset.exists_lt_of_sum_lt (by simpa using hy :
      ∑ x' ∈ Finset.univ, (0 : ℝ) < ∑ x' ∈ Finset.univ, p x' * Px x' y)
    exact (hPpos x y hx).2.1
  rw [hB]
  linarith

/-- `I(X; Y_1) ≤ β` when every relative entropy between conditional laws is at most `β`. -/
theorem mi1_le_b (p : α → ℝ) (q : α → β → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq0 : ∀ x c, 0 ≤ q x c) (hac : ∀ x x' c, 0 < q x c → 0 < q x' c) (b : ℝ)
    (hb : ∀ x x', ∑ c, q x c * log (q x c / q x' c) ≤ b) :
    ∑ z : α × β, p z.1 * q z.1 z.2 *
        log (p z.1 * q z.1 z.2 / (p z.1 * ∑ x', p x' * q x' z.2)) ≤ b := by
  classical
  have hterm : ∀ x c, p x * q x c * log (p x * q x c / (p x * ∑ x', p x' * q x' c)) ≤
      p x * ∑ x', p x' * (q x c * log (q x c / q x' c)) := by
    intro x c
    rcases eq_or_lt_of_le (hp0 x) with h0 | hpx
    · rw [← h0]
      simp
    rcases eq_or_lt_of_le (hq0 x c) with h0 | hqc
    · rw [← h0]
      simp
    have hall : ∀ x', 0 < q x' c := fun x' => hac x x' c hqc
    have hmix := log_mix_ge p (fun x' => q x' c) hp0 hp1 hall
    have hP : 0 < ∑ x', p x' * q x' c := lt_of_lt_of_le (mul_pos hpx hqc)
      (Finset.single_le_sum (f := fun x' => p x' * q x' c)
        (fun x' _ => mul_nonneg (hp0 x') (hq0 x' c)) (Finset.mem_univ x))
    rw [mul_div_mul_left _ _ hpx.ne', log_div hqc.ne' hP.ne']
    have e : ∑ x', p x' * (q x c * log (q x c / q x' c)) =
        q x c * (log (q x c) - ∑ x', p x' * log (q x' c)) := by
      have : ∀ x', p x' * (q x c * log (q x c / q x' c)) =
          q x c * (p x' * log (q x c)) - q x c * (p x' * log (q x' c)) := fun x' => by
        rw [log_div hqc.ne' (hall x').ne']
        ring
      rw [Finset.sum_congr rfl fun x' _ => this x', Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.sum_mul, hp1, one_mul, mul_sub]
    rw [e]
    have := mul_le_mul_of_nonneg_left hmix (mul_nonneg hpx.le hqc.le)
    nlinarith
  calc ∑ z : α × β, p z.1 * q z.1 z.2 * log (p z.1 * q z.1 z.2 / (p z.1 * ∑ x', p x' * q x' z.2))
      ≤ ∑ z : α × β, p z.1 * ∑ x', p x' * (q z.1 z.2 * log (q z.1 z.2 / q x' z.2)) :=
        Finset.sum_le_sum fun z _ => hterm z.1 z.2
    _ = ∑ x, p x * ∑ x', p x' * ∑ c, q x c * log (q x c / q x' c) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, p x * ∑ x', p x' * b := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hb x x') (hp0 x')) (hp0 x)
    _ = b := by
        simp_rw [← Finset.sum_mul, hp1, one_mul]

end Samples

section Assembly

variable {α γ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

theorem ac_prod_marginals (ν : Measure (α × γ)) [IsProbabilityMeasure ν] :
    ν ≪ ν.fst.prod ν.snd := by
  have hle_fst : ∀ a c, ν.real {(a, c)} ≤ ν.fst.real {a} := fun a c => by
    rw [fst_real_singleton]
    exact Finset.single_le_sum (f := fun c => ν.real {(a, c)})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ c)
  have hle_snd : ∀ a c, ν.real {(a, c)} ≤ ν.snd.real {c} := fun a c => by
    rw [snd_real_singleton]
    exact Finset.single_le_sum (f := fun a => ν.real {(a, c)})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ a)
  exact ac_of_singleton fun ⟨a, c⟩ h => by
    have h1 : (ν.fst.prod ν.snd).real {(a, c)} = 0 := by rw [Measure.real, h]; rfl
    rw [prod_real_singleton] at h1
    have h2 : ν.real {(a, c)} = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact le_antisymm (h3 ▸ hle_fst a c) measureReal_nonneg
      · exact le_antisymm (h3 ▸ hle_snd a c) measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top ν _)).mp h2

theorem mutualInfo_sum (ν : Measure (α × γ)) [IsProbabilityMeasure ν] :
    (mutualInfo ν).toReal =
      ∑ z : α × γ, ν.real {z} * log (ν.real {z} / (ν.fst.real {z.1} * ν.snd.real {z.2})) := by
  obtain ⟨-, heq⟩ := klDiv_fintype ν (ν.fst.prod ν.snd) (ac_prod_marginals ν)
  unfold mutualInfo
  rw [heq]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, c⟩ -
  rw [prod_real_singleton]

end Assembly

theorem independent_samples_fano : IndependentSamplesFano.{u} := by
  intro α β γ _ _ _ _ _ _ _ n μX _ η μ _ μ₁ _ κ _ R pmin pmax b hη hμ hμ₁ hac hb hR hpmin hpmax
    hsum hbd
  classical
  have hp0 : ∀ x, 0 ≤ μX.real {x} := fun x => measureReal_nonneg
  have hp1 : ∑ x, μX.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hq0 : ∀ x c, 0 ≤ (η x).real {c} := fun x c => measureReal_nonneg
  have hq1 : ∀ x, ∑ c, (η x).real {c} = 1 := fun x => by
    have := hη x
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hμfst : ∀ x, μ.fst.real {x} = μX.real {x} := fun x => by
    rw [fst_real_singleton]
    simp_rw [hμ]
    rw [← Finset.mul_sum, sum_prod_eq_one _ (hq1 x), mul_one]
  have hμsnd : ∀ y, μ.snd.real {y} = ∑ x', μX.real {x'} * ∏ i, (η x').real {y i} := fun y => by
    rw [snd_real_singleton]
    simp_rw [hμ]
  have hμ₁fst : ∀ x, μ₁.fst.real {x} = μX.real {x} := fun x => by
    rw [fst_real_singleton]
    simp_rw [hμ₁]
    rw [← Finset.mul_sum, hq1 x, mul_one]
  have hμ₁snd : ∀ c, μ₁.snd.real {c} = ∑ x', μX.real {x'} * (η x').real {c} := fun c => by
    rw [snd_real_singleton]
    simp_rw [hμ₁]
  have hIμ : (mutualInfo μ).toReal = ∑ z : α × (Fin n → β), μX.real {z.1} *
      (∏ i, (η z.1).real {z.2 i}) * log (μX.real {z.1} * (∏ i, (η z.1).real {z.2 i}) /
        (μX.real {z.1} * ∑ x', μX.real {x'} * ∏ i, (η x').real {z.2 i})) := by
    rw [mutualInfo_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨x, y⟩ -
    simp only
    rw [hμ x y, hμfst x, hμsnd y]
  have hIμ₁ : (mutualInfo μ₁).toReal = ∑ z : α × β, μX.real {z.1} * (η z.1).real {z.2} *
      log (μX.real {z.1} * (η z.1).real {z.2} /
        (μX.real {z.1} * ∑ x', μX.real {x'} * (η x').real {z.2})) := by
    rw [mutualInfo_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨x, c⟩ -
    simp only
    rw [hμ₁ x c, hμ₁fst x, hμ₁snd c]
  have hIY : (mutualInfo μ).toReal ≤ n * (mutualInfo μ₁).toReal := by
    rw [hIμ, hIμ₁]
    exact samples_mi_le (n := n) (fun x => μX.real {x}) (fun x c => (η x).real {c}) hp0 hp1 hq0
      hq1
  have hacq : ∀ x x' c, 0 < (η x).real {c} → 0 < (η x').real {c} := by
    intro x x' c h
    have := hη x
    have := hη x'
    rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ (η x').real {c}) with h0 | h0
    · exfalso
      have h1 : (η x') {c} = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0.symm
      have h2 : (η x).real {c} = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (hac x x' h1)
      linarith
    · exact h0
  have hbq : ∀ x x', ∑ c, (η x).real {c} * log ((η x).real {c} / (η x').real {c}) ≤ b := by
    intro x x'
    have := hη x
    have := hη x'
    obtain ⟨-, heq⟩ := klDiv_fintype (η x) (η x') (hac x x')
    rw [← heq]
    exact hb x x'
  have hI1b : (mutualInfo μ₁).toReal ≤ b := by
    rw [hIμ₁]
    exact mi1_le_b (fun x => μX.real {x}) (fun x c => (η x).real {c}) hp0 hp1 hq0 hacq b hbq
  have hfin : mutualInfo μ ≠ ∞ := (mutual_info_entropy μ).1
  obtain ⟨h1, h2⟩ := fano_arbitrary_relation μ κ R pmin pmax hR hpmin hpmax hsum hbd hfin
  have hL : 0 < log ((1 - pmin) / pmax) := by
    apply Real.log_pos
    rw [one_lt_div hpmax]
    linarith
  constructor
  · calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hL.le
  · apply div_le_div_of_nonneg_right _ hL.le
    have : (n : ℝ) * (mutualInfo μ₁).toReal ≤ n * b :=
      mul_le_mul_of_nonneg_left hI1b (Nat.cast_nonneg n)
    linarith

end Proof

end Lemmata.FanoDiffusion
