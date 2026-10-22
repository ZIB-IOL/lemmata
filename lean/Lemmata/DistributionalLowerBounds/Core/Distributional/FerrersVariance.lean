module

public import Lemmata.DistributionalLowerBounds.Core.Distributional.FiniteVariance

@[expose] public section

/-! Rank variance of a uniform nested-permutation posterior. -/

namespace Lemmata.DistributionalLowerBounds.Core.Distributional

noncomputable def ferrersRankVariance {m : ℕ} (D : FerrersData m) (i : Fin m) : ℝ :=
  uniformVariance (fun sigma : FerrersPerm D => ((sigma.1 i).val : ℝ))

noncomputable def ferrersTotalRankVariance {m : ℕ} (D : FerrersData m) : ℝ :=
  ∑ i, ferrersRankVariance D i

lemma allowedLast_variance {n : ℕ} (D : FerrersData (n + 1)) :
    uniformVariance (fun p : D.AllowedLast => (p.1.val : ℝ)) =
      ((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12 := by
  letI : Nonempty D.AllowedLast := ⟨⟨D.lastThreshold, by
    change D.lastThreshold ≤ D.lastThreshold
    exact le_rfl⟩⟩
  letI : Nonempty (Fin (D.choices (Fin.last n))) :=
    ⟨⟨0, D.choices_pos _⟩⟩
  have he := uniformVariance_comp_equiv D.allowedLastEquivFin.symm
    (fun p : D.AllowedLast => (p.1.val : ℝ))
  calc
    uniformVariance (fun p : D.AllowedLast => (p.1.val : ℝ)) =
        uniformVariance (fun q : Fin (D.choices (Fin.last n)) =>
          (D.lower (Fin.last n) : ℝ) + q.val) := by
            rw [← he]
            congr 1
            funext q
            rw [D.allowedLastEquivFin_symm_val]
            push_cast
            ring
    _ = uniformVariance (fun q : Fin (D.choices (Fin.last n)) => (q.val : ℝ)) :=
      uniformVariance_add_const _ _
    _ = _ := uniformVariance_fin_val (D.choices_pos _)

lemma castSucc_rankVariance_ge {n : ℕ} (D : FerrersData (n + 1)) (i : Fin n) :
    ferrersRankVariance D i.castSucc ≥ ferrersRankVariance D.dropLast i := by
  let A := D.AllowedLast
  let B := FerrersPerm D.dropLast
  letI : Nonempty A := ⟨⟨D.lastThreshold, by
    change D.lastThreshold ≤ D.lastThreshold
    exact le_rfl⟩⟩
  let Y : A × B → ℝ := fun pe =>
    ((extendLast pe.1.1 pe.2.1 i.castSucc).val : ℝ)
  have htransport : ferrersRankVariance D i.castSucc = uniformVariance Y := by
    unfold ferrersRankVariance
    symm
    exact uniformVariance_comp_equiv (FerrersPerm.decompose D)
      (fun sigma : FerrersPerm D => ((sigma.1 i.castSucc).val : ℝ))
  rw [htransport]
  calc
    uniformVariance Y ≥
        (∑ p : A, uniformVariance (fun e : B => Y (p, e))) / Fintype.card A :=
      uniformVariance_product_ge_fiber Y
    _ ≥ (∑ _p : A, ferrersRankVariance D.dropLast i) / Fintype.card A := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro p _
      unfold ferrersRankVariance
      apply uniformVariance_comp_ge
      intro e f
      dsimp [Y]
      simpa only [extendLast_castSucc] using
        succAbove_abs_expands p.1 (e.1 i) (f.1 i)
    _ = ferrersRankVariance D.dropLast i := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hA : (0 : ℝ) < Fintype.card A := card_cast_pos
      field_simp [hA.ne']

lemma last_rankVariance {n : ℕ} (D : FerrersData (n + 1)) :
    ferrersRankVariance D (Fin.last n) =
      ((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12 := by
  let A := D.AllowedLast
  let B := FerrersPerm D.dropLast
  letI : Nonempty A := ⟨⟨D.lastThreshold, by
    change D.lastThreshold ≤ D.lastThreshold
    exact le_rfl⟩⟩
  let X : FerrersPerm D → ℝ := fun sigma => ((sigma.1 (Fin.last n)).val : ℝ)
  let Y : A × B → ℝ := fun pe => (pe.1.1.val : ℝ)
  have htransport : uniformVariance X = uniformVariance Y := by
    symm
    simpa [X, Y] using uniformVariance_comp_equiv (FerrersPerm.decompose D) X
  unfold ferrersRankVariance
  change uniformVariance X = _
  rw [htransport]
  have hf := uniformVariance_fst (B := B) (fun p : A => (p.1.val : ℝ))
  exact hf.trans (allowedLast_variance D)

/-- Full rank-variance bound before Cauchy--Schwarz. -/
theorem ferrersTotalRankVariance_ge : ∀ {m : ℕ} (D : FerrersData m),
    ferrersTotalRankVariance D ≥
      ∑ i, (((D.choices i : ℝ) ^ 2 - 1) / 12)
  | 0, D => by simp [ferrersTotalRankVariance]
  | n + 1, D => by
      unfold ferrersTotalRankVariance
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hprefix := ferrersTotalRankVariance_ge D.dropLast
      have hrows : (∑ i : Fin n, ferrersRankVariance D i.castSucc) ≥
          ∑ i : Fin n, ferrersRankVariance D.dropLast i :=
        Finset.sum_le_sum (fun i _ => castSucc_rankVariance_ge D i)
      have hlast := last_rankVariance D
      have hchoices : ∀ i : Fin n, D.dropLast.choices i = D.choices i.castSucc := by
        intro i
        rfl
      calc
        (∑ i : Fin n, ferrersRankVariance D i.castSucc) +
            ferrersRankVariance D (Fin.last n) ≥
          (∑ i : Fin n, ferrersRankVariance D.dropLast i) +
            (((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12) := by
              exact add_le_add hrows hlast.ge
        _ ≥ (∑ i : Fin n, (((D.dropLast.choices i : ℝ) ^ 2 - 1) / 12)) +
            (((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12) := by
              have hpref' :
                  (∑ i : Fin n, (((D.dropLast.choices i : ℝ) ^ 2 - 1) / 12)) ≤
                    ∑ i : Fin n, ferrersRankVariance D.dropLast i := by
                simpa [ferrersTotalRankVariance] using hprefix
              simpa [add_comm] using
                (add_le_add_right hpref'
                  (((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12))
        _ = (∑ i : Fin n, (((D.choices i.castSucc : ℝ) ^ 2 - 1) / 12)) +
            (((D.choices (Fin.last n) : ℝ) ^ 2 - 1) / 12) := by
              apply congrArg₂ (· + ·) _ rfl
              apply Finset.sum_congr rfl
              intro i _
              rw [hchoices i]

/-- Deficit form of the rank-variance theorem. -/
theorem ferrers_deficit_variance {m : ℕ} (D : FerrersData m) (hm : 0 < m) :
    ((∑ i, ((D.choices i : ℝ) - 1)) ^ 2) / (12 * m) ≤
      ferrersTotalRankVariance D := by
  have harith := deficit_variance_arithmetic hm
    (fun i => (D.choices i : ℝ))
    (fun i => (((D.choices i : ℝ) ^ 2 - 1) / 12))
    (fun i => by
      have hnat : 1 ≤ D.choices i := Nat.succ_le_iff.mpr (D.choices_pos i)
      change (1 : ℝ) ≤ (D.choices i : ℝ)
      exact_mod_cast hnat)
    (fun _ => le_rfl)
  exact harith.trans (ferrersTotalRankVariance_ge D)

/-- Square-root variance bound for any ordered remaining-rank list whose gaps
are at least the corresponding index gaps. -/
theorem ferrers_sqrt_rank_variance
    {m : ℕ} (D : FerrersData m) (hm : 0 < m)
    (rank : Fin m → ℝ) {d : ℝ} (hd : 0 < d)
    (hr0 : ∀ i, 0 ≤ rank i) (hrd : ∀ i, rank i ≤ d)
    (hgap : ∀ i j,
      |(i.val : ℝ) - (j.val : ℝ)| ≤ |rank i - rank j|) :
    ((∑ i, ((D.choices i : ℝ) - 1)) ^ 2) / (48 * m * d) ≤
      ∑ i, uniformVariance (fun sigma : FerrersPerm D =>
        Real.sqrt (rank (sigma.1 i))) := by
  have hcoord : ∀ i,
      ferrersRankVariance D i / (4 * d) ≤
        uniformVariance (fun sigma : FerrersPerm D =>
          Real.sqrt (rank (sigma.1 i))) := by
    intro i
    let c : ℝ := 1 / (2 * Real.sqrt d)
    let X : FerrersPerm D → ℝ := fun sigma => ((sigma.1 i).val : ℝ)
    let Y : FerrersPerm D → ℝ := fun sigma => Real.sqrt (rank (sigma.1 i))
    have hdist : ∀ a b, |c * X a - c * X b| ≤ |Y a - Y b| := by
      intro a b
      have hsqrt := sqrt_difference_lower_bound hd
        (hr0 (a.1 i)) (hr0 (b.1 i)) (hrd (a.1 i)) (hrd (b.1 i))
      have hidx := hgap (a.1 i) (b.1 i)
      have hc : 0 < c := by dsimp [c]; positivity
      have hcform : |rank (a.1 i) - rank (b.1 i)| / (2 * Real.sqrt d) =
          c * |rank (a.1 i) - rank (b.1 i)| := by
        dsimp [c]
        ring
      rw [hcform] at hsqrt
      dsimp [X, Y]
      rw [show c * (a.1 i).val - c * (b.1 i).val =
          c * ((a.1 i).val - (b.1 i).val) by ring, abs_mul,
        abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left hidx hc.le).trans hsqrt
    have hv := uniformVariance_comp_ge (fun s => c * X s) Y hdist
    rw [uniformVariance_const_mul] at hv
    have hc2 : c ^ 2 = 1 / (4 * d) := by
      dsimp [c]
      have hs := Real.sq_sqrt hd.le
      field_simp [hd.ne']
      nlinarith
    rw [hc2] at hv
    change ferrersRankVariance D i / (4 * d) ≤ uniformVariance Y
    dsimp [ferrersRankVariance, X, Y] at hv ⊢
    have heq : (uniformVariance fun sigma : FerrersPerm D =>
        ((sigma.1 i).val : ℝ)) / (4 * d) =
        (1 / (4 * d)) * uniformVariance (fun sigma : FerrersPerm D =>
          ((sigma.1 i).val : ℝ)) := by
      ring
    rw [heq]
    exact hv
  have hsum : ferrersTotalRankVariance D / (4 * d) ≤
      ∑ i, uniformVariance (fun sigma : FerrersPerm D =>
        Real.sqrt (rank (sigma.1 i))) := by
    rw [ferrersTotalRankVariance, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => hcoord i)
  have hdef := ferrers_deficit_variance D hm
  have hd4 : 0 < 4 * d := by positivity
  have hscaled := div_le_div_of_nonneg_right hdef hd4.le
  have heq :
      (((∑ i, ((D.choices i : ℝ) - 1)) ^ 2) / (12 * m)) / (4 * d) =
        ((∑ i, ((D.choices i : ℝ) - 1)) ^ 2) / (48 * m * d) := by ring
  rw [heq] at hscaled
  exact hscaled.trans hsum

/-- Variance scaling for the optimizer coordinates
`rho*C*sqrt(2)*(sqrt(top)-sqrt(rank))`. -/
lemma optimizerCoordinate_variance
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (rho C top : ℝ) :
    uniformVariance (fun ω =>
      rho * C * Real.sqrt 2 * (Real.sqrt top - X ω)) =
      2 * rho ^ 2 * C ^ 2 * uniformVariance X := by
  let a : ℝ := rho * C * Real.sqrt 2
  have hrewrite : (fun ω => a * (Real.sqrt top - X ω)) =
      (fun ω => a * Real.sqrt top + (-a) * X ω) := by
    funext ω
    ring
  rw [show (fun ω => rho * C * Real.sqrt 2 * (Real.sqrt top - X ω)) =
      (fun ω => a * (Real.sqrt top - X ω)) by rfl, hrewrite,
    uniformVariance_add_const, uniformVariance_const_mul]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [a]
  rw [neg_sq, mul_pow, mul_pow, hs]
  ring

/-- Conditional optimization-error theorem for a Ferrers posterior. -/
theorem ferrers_conditional_error
    {m : ℕ} (D : FerrersData m) (hm : 0 < m)
    (rank : Fin m → ℝ) {d rho C top : ℝ} (hd : 0 < d)
    (hr0 : ∀ i, 0 ≤ rank i) (hrd : ∀ i, rank i ≤ d)
    (hgap : ∀ i j,
      |(i.val : ℝ) - (j.val : ℝ)| ≤ |rank i - rank j|)
    (estimate : Fin m → ℝ) (loss : FerrersPerm D → ℝ)
    (hloss : ∀ sigma,
      (1 / 2 : ℝ) * ∑ i,
        (estimate i - rho * C * Real.sqrt 2 *
          (Real.sqrt top - Real.sqrt (rank (sigma.1 i)))) ^ 2 ≤ loss sigma) :
    rho ^ 2 * C ^ 2 *
        (∑ i, ((D.choices i : ℝ) - 1)) ^ 2 / (48 * m * d) ≤
      uniformAverage loss := by
  let target : FerrersPerm D → Fin m → ℝ := fun sigma i =>
    rho * C * Real.sqrt 2 *
      (Real.sqrt top - Real.sqrt (rank (sigma.1 i)))
  have hlossAvg := uniformAverage_loss_ge_totalVariance target estimate loss hloss
  have hvar : ∀ i,
      uniformVariance (fun sigma : FerrersPerm D => target sigma i) =
        2 * rho ^ 2 * C ^ 2 *
          uniformVariance (fun sigma : FerrersPerm D =>
            Real.sqrt (rank (sigma.1 i))) := by
    intro i
    exact optimizerCoordinate_variance _ rho C top
  rw [show (∑ i, uniformVariance (fun sigma : FerrersPerm D => target sigma i)) =
      2 * rho ^ 2 * C ^ 2 *
        ∑ i, uniformVariance (fun sigma : FerrersPerm D =>
          Real.sqrt (rank (sigma.1 i))) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hvar i] at hlossAvg
  have hsqrt := ferrers_sqrt_rank_variance D hm rank hd hr0 hrd hgap
  have hcoef : 0 ≤ rho ^ 2 * C ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsqrt hcoef
  have heq : rho ^ 2 * C ^ 2 *
      (((∑ i, ((D.choices i : ℝ) - 1)) ^ 2) / (48 * m * d)) =
      rho ^ 2 * C ^ 2 *
        (∑ i, ((D.choices i : ℝ) - 1)) ^ 2 / (48 * m * d) := by ring
  rw [heq] at hscaled
  have hlossAvg' : rho ^ 2 * C ^ 2 *
      (∑ i, uniformVariance (fun sigma : FerrersPerm D =>
        Real.sqrt (rank (sigma.1 i)))) ≤ uniformAverage loss := by
    nlinarith [hlossAvg]
  exact hscaled.trans hlossAvg'

end Lemmata.DistributionalLowerBounds.Core.Distributional
