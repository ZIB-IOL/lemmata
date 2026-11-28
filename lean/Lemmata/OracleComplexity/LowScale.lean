module

public import Lemmata.OracleComplexity.Lp

@[expose] public section

/-!
# The low-scale case for `ℓ^p` balls (Proposition V.5)

The cube of side `2ρ`, `ρ = n^{-1/p}`, lies in the unit `ℓ^p` ball, and the hard functions of
Section IV.B rescaled into it, `g_S(x) = ρ f_S(x/ρ)`, keep the Lipschitz constant `1` for the
maximum norm, hence for the `ℓ^p` norm. Their minimizers lie in the ball, so an `ε`-minimizer over
the ball becomes an `(ε/ρ)`-minimizer of `f_S` after rescaling, and the rescaled oracle is emulated
by the oracle of Section IV.B; Theorem IV.2 gives the bound.
-/

namespace Lemmata.OracleComplexity

variable {n M : ℕ} [NeZero n]

omit [NeZero n] in
theorem center_abs_le (S : Fin M → Bool) : |boxCenter S M| ≤ 1 := by
  have h := boxCenter_tail S M 0 (by simp)
  have h0 : boxCenter S 0 = 0 := by simp [boxCenter]
  rw [h0, sub_zero, pow_zero] at h
  have : (0 : ℝ) ≤ (1 / 4) ^ M := by positivity
  linarith

theorem rho_pos (p : ℝ) : 0 < (n : ℝ) ^ (-1 / p) :=
  Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) _

theorem scaled_center_mem {p : ℝ} (hp : 1 ≤ p) (S : Fin n → Fin M → Bool) :
    (fun i => (n : ℝ) ^ (-1 / p) * boxCenter (S i) M) ∈ lpBall p n := by
  have hp0 : 0 < p := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hρ := rho_pos (n := n) p
  have hc : ((n : ℝ) ^ (-1 / p)) ^ p = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_mul hn0.le, show -1 / p * p = -1 by field_simp, Real.rpow_neg_one]
  show ∑ i, |(n : ℝ) ^ (-1 / p) * boxCenter (S i) M| ^ p ≤ 1
  calc ∑ i, |(n : ℝ) ^ (-1 / p) * boxCenter (S i) M| ^ p
      ≤ ∑ _i : Fin n, ((n : ℝ) ^ (-1 / p)) ^ p := by
        refine Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (abs_nonneg _) ?_ hp0.le)
        rw [abs_mul, abs_of_pos hρ]
        exact mul_le_of_le_one_right hρ.le (center_abs_le _)
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
        field_simp

theorem scaled_at (ρ : ℝ) (hρ : 0 < ρ) (S : Fin n → Fin M → Bool) :
    scaledFn ρ S (fun i => ρ * boxCenter (S i) M) = ρ * (boxLevel M - (1 / 8) ^ M) := by
  unfold scaledFn
  congr 1
  rw [← cube_at_center S]
  congr 1
  funext i
  field_simp

theorem scaled_min (ρ : ℝ) (hρ : 0 < ρ) (S : Fin n → Fin M → Bool) (y : Fin n → ℝ) :
    ρ * (boxLevel M - (1 / 8) ^ M) ≤ scaledFn ρ S y :=
  mul_le_mul_of_nonneg_left (cube_min S _) hρ.le

namespace Proof

theorem low_scale_lower_bound : LowScaleLowerBound := by
  classical
  intro n M _ p ε hp hε ρ
  have hρ : 0 < ρ := rho_pos p
  have hvalid := Proof.cube_oracle_valid n M
  refine ⟨fun S => ⟨?_, fun x y => ?_, fun x => ⟨rfl, fun y => ?_⟩, ?_⟩, fun t => ?_⟩
  · -- convexity
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := (hvalid S).1.2 (Set.mem_univ (fun i => x i / ρ)) (Set.mem_univ (fun i => y i / ρ))
      ha hb hab
    have he : (fun i => (a • x + b • y) i / ρ) =
        a • (fun i => x i / ρ) + b • (fun i => y i / ρ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ρ * cubeFn S (fun i => (a • x + b • y) i / ρ) ≤ a • (ρ * cubeFn S (fun i => x i / ρ)) +
      b • (ρ * cubeFn S (fun i => y i / ρ))
    rw [he]
    simp only [smul_eq_mul] at this ⊢
    nlinarith
  · -- the Lipschitz bound
    have hL := (hvalid S).2.1
    set D := (∑ i, |x i - y i| ^ p) ^ (1 / p) with hD
    have hD0 : 0 ≤ D := Real.rpow_nonneg (Finset.sum_nonneg (fun i _ =>
      Real.rpow_nonneg (abs_nonneg _) _)) _
    have hdist : dist (fun i => x i / ρ) (fun i => y i / ρ) ≤ D / ρ := by
      refine (dist_pi_le_iff (by positivity)).mpr (fun i => ?_)
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]
      exact div_le_div_of_nonneg_right (coord_le_lp hp x y i) hρ.le
    have h1 := hL.dist_le_mul (fun i => x i / ρ) (fun i => y i / ρ)
    rw [Real.dist_eq] at h1
    simp only [NNReal.coe_one, one_mul] at h1
    show |ρ * cubeFn S (fun i => x i / ρ) - ρ * cubeFn S (fun i => y i / ρ)| ≤ D
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    calc ρ * |cubeFn S (fun i => x i / ρ) - cubeFn S (fun i => y i / ρ)|
        ≤ ρ * (D / ρ) := mul_le_mul_of_nonneg_left (h1.trans hdist) hρ.le
      _ = D := by field_simp
  · -- the subgradient
    have h1 := ((hvalid S).2.2 (fun i => x i / ρ)).2 (fun i => y i / ρ)
    rw [((hvalid S).2.2 (fun i => x i / ρ)).1.symm] at h1
    show ρ * (cubeOracle S (fun i => x i / ρ)).1 + (cubeOracle S (fun i => x i / ρ)).2.2 *
      (y (cubeOracle S (fun i => x i / ρ)).2.1 - x (cubeOracle S (fun i => x i / ρ)).2.1) ≤
        ρ * cubeFn S (fun i => y i / ρ)
    have h2 := mul_le_mul_of_nonneg_left h1 hρ.le
    have h3 : ρ * ((cubeOracle S (fun i => x i / ρ)).2.2 *
        (y (cubeOracle S (fun i => x i / ρ)).2.1 / ρ -
          x (cubeOracle S (fun i => x i / ρ)).2.1 / ρ)) =
        (cubeOracle S (fun i => x i / ρ)).2.2 *
          (y (cubeOracle S (fun i => x i / ρ)).2.1 - x (cubeOracle S (fun i => x i / ρ)).2.1) := by
      field_simp
    rw [mul_add, h3] at h2
    exact h2
  · -- the minimizer in the ball
    refine ⟨fun i => ρ * boxCenter (S i) M, scaled_center_mem hp S, fun y => ?_⟩
    rw [scaled_at ρ hρ S]
    exact scaled_min ρ hρ S y
  · -- the lower bound, through the oracle of Section IV.B
    intro Pe
    obtain ⟨t', ht'⟩ := Proof.emulation (fun S : Fin n → Fin M → Bool => scaledOracle ρ S)
      (fun S : Fin n → Fin M → Bool => cubeOracle S) (fun x i => x i / ρ)
      (fun _ a => (ρ * a.1, a.2)) (fun S x => rfl) t
    set t'' := mapOut (fun y : Fin n → ℝ => fun i => y i / ρ) t' with ht''
    have hε' : ε / ρ < (1 / 8) ^ M := by
      rw [div_lt_iff₀ hρ]; linarith [mul_comm ρ ((1 / 8 : ℝ) ^ M)]
    have hcube := Proof.cube_lower_bound n M (ε / ρ) hε' t''
    have hq : ∀ S : Fin n → Fin M → Bool,
        t''.queries (cubeOracle S) = t.queries (scaledOracle ρ S) := by
      intro S
      rw [ht'', (mapOut_spec _ _ t').2, (ht' S).2]
    have hout : ∀ S : Fin n → Fin M → Bool,
        t''.output (cubeOracle S) = fun i => t.output (scaledOracle ρ S) i / ρ := by
      intro S
      rw [ht'', (mapOut_spec _ _ t').1, (ht' S).1]
    simp only [hq, hout] at hcube
    refine le_trans ?_ hcube
    have hcard : ((Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
        ¬ ∀ y, cubeFn S (fun i => t.output (scaledOracle ρ S) i / ρ) ≤
          cubeFn S y + ε / ρ)).card : ℝ) ≤
        ((Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
          ¬ (t.output (scaledOracle ρ S) ∈ lpBall p n ∧ ∀ y ∈ lpBall p n,
            scaledFn ρ S (t.output (scaledOracle ρ S)) ≤ scaledFn ρ S y + ε))).card : ℝ) := by
      have hsub : Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
          ¬ ∀ y, cubeFn S (fun i => t.output (scaledOracle ρ S) i / ρ) ≤ cubeFn S y + ε / ρ) ⊆
          Finset.univ.filter (fun S : Fin n → Fin M → Bool =>
            ¬ (t.output (scaledOracle ρ S) ∈ lpBall p n ∧ ∀ y ∈ lpBall p n,
              scaledFn ρ S (t.output (scaledOracle ρ S)) ≤ scaledFn ρ S y + ε)) := by
        intro S hS
        rw [Finset.mem_filter] at hS ⊢
        refine ⟨Finset.mem_univ _, fun hopt => hS.2 (fun y => ?_)⟩
        have h1 := hopt.2 _ (scaled_center_mem hp S)
        rw [scaled_at ρ hρ S] at h1
        have h2 := cube_min S y
        unfold scaledFn at h1
        have h3 : cubeFn S (fun i => t.output (scaledOracle ρ S) i / ρ) ≤
            boxLevel M - (1 / 8) ^ M + ε / ρ := by
          rw [← mul_le_mul_iff_of_pos_left hρ, mul_add, mul_div_cancel₀ _ hρ.ne']
          exact h1
        linarith
      exact_mod_cast Finset.card_le_card hsub
    have hpos : (0 : ℝ) < 2 ^ (n * M) := by positivity
    have hnM : (0 : ℝ) ≤ (n : ℝ) * M := by positivity
    have h1 := div_le_div_of_nonneg_right hcard hpos.le
    have := mul_le_mul_of_nonneg_right h1 hnM
    simp only [Pe]
    linarith

end Proof

end Lemmata.OracleComplexity
