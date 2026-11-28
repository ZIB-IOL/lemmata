module

public import Lemmata.OracleComplexity.BoxLocal

@[expose] public section

/-!
# The hard functions of Section IV.B

The hard function of `S₁, …, Sₙ` is the maximum of the one-dimensional hard functions of the
coordinates. Its `ε`-minimizers have `ε`-minimal coordinates, which decode the strings (Lemma IV.6).
Moving one coordinate changes the value only through that coordinate: an active coordinate
strictly increases the value in the direction of its oracle slope, at that rate, and an inactive
coordinate leaves the value unchanged nearby. So the active coordinates, the least of them and its
oracle slope are determined by the function near `x`, and the oracle is local.
-/

namespace Lemmata.OracleComplexity

variable {n M : ℕ} [NeZero n]

theorem coord_le_cube (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n) :
    boxFn (S i) (x i) ≤ cubeFn S x :=
  Finset.le_sup' (fun i => boxFn (S i) (x i)) (Finset.mem_univ i)

open Classical in
theorem cubeCoord_spec (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) :
    boxFn (S (cubeCoord S x)) (x (cubeCoord S x)) = cubeFn S x ∧
      ∀ i, boxFn (S i) (x i) = cubeFn S x → cubeCoord S x ≤ i := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := Finset.min'_mem (Finset.univ.filter (fun i => boxFn (S i) (x i) = cubeFn S x)) (by
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun i => boxFn (S i) (x i))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm⟩⟩)
    exact (Finset.mem_filter.mp this).2
  · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem box_convex (S : Fin M → Bool) : ConvexOn ℝ Set.univ (boxFn S) :=
  (Proof.box_oracle_valid M S).1

theorem box_lipschitz (S : Fin M → Bool) : LipschitzWith 1 (boxFn S) :=
  (Proof.box_oracle_valid M S).2.1

theorem box_le_add_abs (S : Fin M → Bool) (x y : ℝ) : boxFn S x ≤ boxFn S y + |x - y| := by
  have h := (box_lipschitz S).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  linarith [le_abs_self (boxFn S x - boxFn S y)]

/-- The value after moving coordinate `i` to `z` is at most the larger of the new value of that
coordinate and the old maximum. -/
theorem cube_update_le (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n) (z : ℝ) :
    cubeFn S (Function.update x i z) ≤ max (boxFn (S i) z) (cubeFn S x) := by
  apply Finset.sup'_le
  intro j _
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact le_max_left _ _
  · rw [Function.update_of_ne hj]
    exact (coord_le_cube S x j).trans (le_max_right _ _)

theorem cube_update_ge (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n) (z : ℝ) :
    boxFn (S i) z ≤ cubeFn S (Function.update x i z) := by
  have := coord_le_cube S (Function.update x i z) i
  rwa [Function.update_self] at this

/-- Moving an inactive coordinate within the gap leaves the value unchanged. -/
theorem cube_update_inactive (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n) (z : ℝ)
    (hi : boxFn (S i) (x i) ≠ cubeFn S x) (hz : boxFn (S i) z ≤ cubeFn S x) :
    cubeFn S (Function.update x i z) = cubeFn S x := by
  apply le_antisymm ((cube_update_le S x i z).trans (max_le hz le_rfl))
  obtain ⟨hc, -⟩ := cubeCoord_spec S x
  have hne : cubeCoord S x ≠ i := fun e => hi (e ▸ hc)
  have := coord_le_cube S (Function.update x i z) (cubeCoord S x)
  rwa [Function.update_of_ne hne, hc] at this

namespace Proof

theorem cube_oracle_valid : CubeOracleValid := by
  intro n M _ S
  refine ⟨?_, ?_, fun x => ⟨rfl, fun y => ?_⟩⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain ⟨i, -, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => boxFn (S i) ((a • x + b • y) i))
    have hc := (box_convex (S i)).2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) ha hb hab
    show cubeFn S (a • x + b • y) ≤ a • cubeFn S x + b • cubeFn S y
    have k1 := mul_le_mul_of_nonneg_left (coord_le_cube S x i) ha
    have k2 := mul_le_mul_of_nonneg_left (coord_le_cube S y i) hb
    have hval : cubeFn S (a • x + b • y) = boxFn (S i) (a * x i + b * y i) := by
      unfold cubeFn
      rw [hmax]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hval]
    simp only [smul_eq_mul] at hc ⊢
    linarith
  · apply LipschitzWith.of_le_add_mul
    intro x y
    apply Finset.sup'_le
    intro i _
    have h1 := box_le_add_abs (S i) (x i) (y i)
    have h2 : |x i - y i| ≤ dist x y := by
      rw [← Real.dist_eq]
      exact dist_le_pi_dist x y i
    have h3 := coord_le_cube S y i
    simp only [NNReal.coe_one, one_mul]
    linarith
  · obtain ⟨hc, -⟩ := cubeCoord_spec S x
    have h1 := boxOracle_subgrad (S (cubeCoord S x)) (x (cubeCoord S x)) (y (cubeCoord S x))
    have h2 := coord_le_cube S y (cubeCoord S x)
    show cubeFn S x + (boxOracle (S (cubeCoord S x)) (x (cubeCoord S x))).2 *
      (y (cubeCoord S x) - x (cubeCoord S x)) ≤ cubeFn S y
    rw [← hc]
    linarith

end Proof

theorem cube_min (S : Fin n → Fin M → Bool) (y : Fin n → ℝ) :
    boxLevel M - (1 / 8) ^ M ≤ cubeFn S y := by
  have i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  exact (box_min (S i₀) (y i₀)).trans (coord_le_cube S y i₀)

theorem cube_at_center (S : Fin n → Fin M → Bool) :
    cubeFn S (fun i => boxCenter (S i) M) = boxLevel M - (1 / 8) ^ M :=
  le_antisymm (Finset.sup'_le _ _ (fun i _ => (box_at_center (S i)).le)) (cube_min S _)

/-- The coordinates of an `ε`-minimizer decode the strings. -/
theorem cube_decode {S : Fin n → Fin M → Bool} {ε : ℝ} {x : Fin n → ℝ} (hε : ε < (1 / 8) ^ M)
    (hopt : ∀ y, cubeFn S x ≤ cubeFn S y + ε) : ∀ i (k : Fin M), pathBit (x i) k = S i k := by
  intro i k
  have hi : ∀ y, boxFn (S i) (x i) ≤ boxFn (S i) y + ε := by
    intro y
    have h1 := coord_le_cube S x i
    have h2 := hopt (fun i => boxCenter (S i) M)
    rw [cube_at_center] at h2
    have h3 := box_min (S i) y
    linarith
  exact path_of_near (near_of_opt hε hi) k

namespace Proof

theorem cube_packing : CubePacking := by
  intro n M _ S
  refine ⟨cube_min S, cube_at_center S, fun S' ε x hε hS hS' => ?_⟩
  funext i k
  rw [← cube_decode hε hS i k, cube_decode hε hS' i k]

end Proof

/-- An active coordinate strictly increases the value when moved in some direction. -/
theorem active_moves (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n)
    (hi : boxFn (S i) (x i) = cubeFn S x) : ∃ δ > 0,
      (∀ t, 0 < t → t ≤ δ → cubeFn S x < cubeFn S (Function.update x i (x i + t))) ∨
      (∀ t, 0 < t → t ≤ δ → cubeFn S x < cubeFn S (Function.update x i (x i - t))) := by
  by_cases hR : 0 < boxRight (S i) (x i)
  · obtain ⟨δ, hδ, h⟩ := box_right_affine (S i) (x i)
    refine ⟨δ, hδ, Or.inl fun t ht htδ => ?_⟩
    have h1 := cube_update_ge S x i (x i + t)
    rw [h t ht htδ, hi] at h1
    have : 0 < t * boxRight (S i) (x i) := mul_pos ht hR
    linarith
  · have hL : boxLeft (S i) (x i) < 0 :=
      lt_of_le_of_ne ((boxLeft_le_boxRight _ _).trans (not_lt.mp hR)) (boxLeft_ne_zero _ _)
    obtain ⟨δ, hδ, h⟩ := box_left_affine (S i) (x i)
    refine ⟨δ, hδ, Or.inr fun t ht htδ => ?_⟩
    have h1 := cube_update_ge S x i (x i - t)
    rw [h t ht htδ, hi] at h1
    have : t * boxLeft (S i) (x i) < 0 := mul_neg_of_pos_of_neg ht hL
    linarith

/-- An inactive coordinate leaves the value unchanged when moved a little. -/
theorem inactive_still (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n)
    (hi : boxFn (S i) (x i) ≠ cubeFn S x) : ∃ δ > 0, ∀ t, |t| ≤ δ →
      cubeFn S (Function.update x i (x i + t)) = cubeFn S x := by
  have hlt : boxFn (S i) (x i) < cubeFn S x := lt_of_le_of_ne (coord_le_cube S x i) hi
  refine ⟨cubeFn S x - boxFn (S i) (x i), by linarith, fun t ht => ?_⟩
  apply cube_update_inactive S x i _ hi
  have := box_le_add_abs (S i) (x i + t) (x i)
  rw [add_sub_cancel_left] at this
  linarith

/-- With a positive right derivative, an active coordinate raises the value at that rate. -/
theorem active_right_rate (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n)
    (hi : boxFn (S i) (x i) = cubeFn S x) : ∃ δ > 0, ∀ t, 0 < t → t ≤ δ →
      (0 < boxRight (S i) (x i) → cubeFn S (Function.update x i (x i + t)) =
        cubeFn S x + t * boxRight (S i) (x i)) ∧
      (boxRight (S i) (x i) ≤ 0 → cubeFn S (Function.update x i (x i + t)) ≤ cubeFn S x) := by
  obtain ⟨δ, hδ, h⟩ := box_right_affine (S i) (x i)
  refine ⟨δ, hδ, fun t ht htδ => ⟨fun hR => ?_, fun hR => ?_⟩⟩
  · apply le_antisymm
    · refine (cube_update_le S x i _).trans (max_le ?_ ?_)
      · rw [h t ht htδ, hi]
      · have : 0 < t * boxRight (S i) (x i) := mul_pos ht hR
        linarith
    · have := cube_update_ge S x i (x i + t)
      rwa [h t ht htδ, hi] at this
  · refine (cube_update_le S x i _).trans (max_le ?_ le_rfl)
    rw [h t ht htδ, hi]
    have : t * boxRight (S i) (x i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hR
    linarith

/-- With a negative left derivative, an active coordinate raises the value to the left at that
rate. -/
theorem active_left_rate (S : Fin n → Fin M → Bool) (x : Fin n → ℝ) (i : Fin n)
    (hi : boxFn (S i) (x i) = cubeFn S x) (hL : boxLeft (S i) (x i) < 0) : ∃ δ > 0,
      ∀ t, 0 < t → t ≤ δ → cubeFn S (Function.update x i (x i - t)) =
        cubeFn S x - t * boxLeft (S i) (x i) := by
  obtain ⟨δ, hδ, h⟩ := box_left_affine (S i) (x i)
  refine ⟨δ, hδ, fun t ht htδ => le_antisymm ?_ ?_⟩
  · refine (cube_update_le S x i _).trans (max_le ?_ ?_)
    · rw [h t ht htδ, hi]
    · have : t * boxLeft (S i) (x i) < 0 := mul_neg_of_pos_of_neg ht hL
      linarith
  · have := cube_update_ge S x i (x i - t)
    rwa [h t ht htδ, hi] at this

omit [NeZero n] in
theorem dist_update (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    dist (Function.update x i (x i + t)) x = |t| := by
  have h : Function.update x i (x i + t) = x + Pi.single i t := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [h, dist_eq_norm, add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs]

namespace Proof

theorem cube_local : CubeLocal := by
  intro n M _ S S' x h
  obtain ⟨ε, hε, hU⟩ := Metric.eventually_nhds_iff.mp h
  have hU' : ∀ i : Fin n, ∀ t, |t| < ε →
      cubeFn S (Function.update x i (x i + t)) = cubeFn S' (Function.update x i (x i + t)) :=
    fun i t ht => hU (by rw [dist_update]; exact ht)
  have hx : cubeFn S x = cubeFn S' x := hU (by simpa using hε)
  -- the same coordinates attain the maximum
  have hact : ∀ (T T' : Fin n → Fin M → Bool),
      (∀ i : Fin n, ∀ t, |t| < ε →
        cubeFn T (Function.update x i (x i + t)) = cubeFn T' (Function.update x i (x i + t))) →
      cubeFn T x = cubeFn T' x →
      ∀ i, boxFn (T i) (x i) = cubeFn T x → boxFn (T' i) (x i) = cubeFn T' x := by
    intro T T' hTT hTx i hi
    by_contra hi'
    obtain ⟨δ₁, hδ₁, h1⟩ := active_moves T x i hi
    obtain ⟨δ₂, hδ₂, h2⟩ := inactive_still T' x i hi'
    set t := min (min δ₁ δ₂) (ε / 2) with htdef
    have ht : 0 < t := lt_min (lt_min hδ₁ hδ₂) (by linarith)
    have htε : t < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have t1 : t ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have t2 : t ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
    rcases h1 with h1 | h1
    · have e1 := h1 t ht t1
      have e2 := h2 t (by rw [abs_of_pos ht]; exact t2)
      rw [hTT i t (by rw [abs_of_pos ht]; exact htε), e2, ← hTx] at e1
      exact lt_irrefl _ e1
    · have e1 := h1 t ht t1
      have e2 := h2 (-t) (by rw [abs_neg, abs_of_pos ht]; exact t2)
      rw [← sub_eq_add_neg] at e2
      have e3 := hTT i (-t) (by rw [abs_neg, abs_of_pos ht]; exact htε)
      rw [← sub_eq_add_neg] at e3
      rw [e3, e2, ← hTx] at e1
      exact lt_irrefl _ e1
  have hiff : ∀ i, boxFn (S i) (x i) = cubeFn S x ↔ boxFn (S' i) (x i) = cubeFn S' x :=
    fun i => ⟨hact S S' hU' hx i, hact S' S (fun i t ht => (hU' i t ht).symm) hx.symm i⟩
  -- the same least active coordinate
  have hc : cubeCoord S x = cubeCoord S' x := by
    obtain ⟨h1, h2⟩ := cubeCoord_spec S x
    obtain ⟨h1', h2'⟩ := cubeCoord_spec S' x
    exact le_antisymm (h2 _ ((hiff _).mpr h1')) (h2' _ ((hiff _).mp h1))
  set c := cubeCoord S x with hcdef
  have hcS : boxFn (S c) (x c) = cubeFn S x := (cubeCoord_spec S x).1
  have hcS' : boxFn (S' c) (x c) = cubeFn S' x := by rw [hc]; exact (cubeCoord_spec S' x).1
  -- the same oracle slope
  obtain ⟨δ₁, hδ₁, hr⟩ := active_right_rate S x c hcS
  obtain ⟨δ₂, hδ₂, hr'⟩ := active_right_rate S' x c hcS'
  set t := min (min δ₁ δ₂) (ε / 2) with htdef
  have ht : 0 < t := lt_min (lt_min hδ₁ hδ₂) (by linarith)
  have htε : |t| < ε := by rw [abs_of_pos ht]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have t1 : t ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have t2 : t ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have heqt := hU' c t htε
  have hslope : (boxOracle (S c) (x c)).2 = (boxOracle (S' c) (x c)).2 := by
    unfold boxOracle
    simp only
    by_cases hR : 0 < boxRight (S c) (x c)
    · have e1 := (hr t ht t1).1 hR
      by_cases hR' : 0 < boxRight (S' c) (x c)
      · have e2 := (hr' t ht t2).1 hR'
        rw [ite_eq_left hR, ite_eq_left hR']
        rw [e1, e2, hx] at heqt
        exact mul_left_cancel₀ ht.ne' (by linarith)
      · exfalso
        have e2 := (hr' t ht t2).2 (not_lt.mp hR')
        rw [e1, hx] at heqt
        have : 0 < t * boxRight (S c) (x c) := mul_pos ht hR
        linarith
    · by_cases hR' : 0 < boxRight (S' c) (x c)
      · exfalso
        have e1 := (hr t ht t1).2 (not_lt.mp hR)
        have e2 := (hr' t ht t2).1 hR'
        rw [e2, ← hx] at heqt
        have : 0 < t * boxRight (S' c) (x c) := mul_pos ht hR'
        linarith
      · rw [ite_eq_right hR, ite_eq_right hR']
        have hL : boxLeft (S c) (x c) < 0 :=
          lt_of_le_of_ne ((boxLeft_le_boxRight _ _).trans (not_lt.mp hR)) (boxLeft_ne_zero _ _)
        have hL' : boxLeft (S' c) (x c) < 0 :=
          lt_of_le_of_ne ((boxLeft_le_boxRight _ _).trans (not_lt.mp hR')) (boxLeft_ne_zero _ _)
        obtain ⟨δ₃, hδ₃, hl⟩ := active_left_rate S x c hcS hL
        obtain ⟨δ₄, hδ₄, hl'⟩ := active_left_rate S' x c hcS' hL'
        set s := min (min δ₃ δ₄) (ε / 2) with hsdef
        have hs : 0 < s := lt_min (lt_min hδ₃ hδ₄) (by linarith)
        have hsε : |(-s)| < ε := by
          rw [abs_neg, abs_of_pos hs]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have s3 : s ≤ δ₃ := (min_le_left _ _).trans (min_le_left _ _)
        have s4 : s ≤ δ₄ := (min_le_left _ _).trans (min_le_right _ _)
        have heqs := hU' c (-s) hsε
        rw [← sub_eq_add_neg, hl s hs s3, hl' s hs s4, hx] at heqs
        exact mul_left_cancel₀ hs.ne' (by linarith)
  show cubeOracle S x = cubeOracle S' x
  unfold cubeOracle
  rw [hx, ← hc, hslope]

end Proof

end Lemmata.OracleComplexity
