module

public import Lemmata.CommonInformationHsb.Diagonal

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

/-- A product distribution whose support respects block labels is concentrated
in a single common block. -/
theorem product_supported_one_block {I J B : Type*} [Fintype I] [Fintype J]
    {p : I → ℝ} {q : J → ℝ} (hp : IsProbability p) (hq : IsProbability q)
    (f : I → B) (g : J → B)
    (hsupport : ∀ i j, f i ≠ g j → p i * q j = 0) :
    ∃ b, (∀ i, f i ≠ b → p i = 0) ∧ (∀ j, g j ≠ b → q j = 0) := by
  obtain ⟨i, hi⟩ := probability_exists_pos hp
  obtain ⟨j, hj⟩ := probability_exists_pos hq
  have hij : f i = g j := by
    by_contra h
    exact (mul_pos hi hj).ne' (hsupport i j h)
  refine ⟨f i, ?_, ?_⟩
  · intro a ha
    exact (mul_eq_zero.mp (hsupport a j (by rwa [← hij]))).resolve_right (ne_of_gt hj)
  · intro a ha
    exact (mul_eq_zero.mp (hsupport i a (Ne.symm ha))).resolve_left (ne_of_gt hi)

/-- Restriction to the large block preserves probability and entropy when the
singleton coordinates have zero mass. -/
theorem probability_entropy_inl {S r : ℕ} {p : Fin S ⊕ Fin r → ℝ}
    (hp : IsProbability p) (hz : ∀ j, p (.inr j) = 0) :
    IsProbability (fun i => p (.inl i)) ∧ entropy p = entropy (fun i => p (.inl i)) := by
  constructor
  · refine ⟨fun i => hp.1 _, ?_⟩
    simpa [Fintype.sum_sum_type, hz] using hp.2
  · simp [entropy, Fintype.sum_sum_type, hz]

/-- All product distributions on the block support satisfy the sharp
component entropy bound, including those in singleton blocks. -/
theorem product_block_entropy_bound {S r : ℕ} {p q : Fin S ⊕ Fin r → ℝ}
    (hp : IsProbability p) (hq : IsProbability q)
    (hsupport : ∀ i j, blockLabel i ≠ blockLabel j → p i * q j = 0) :
    entropy p + entropy q ≤ (∑ i : Fin S, p (.inl i)) * (2 * Real.log S) := by
  obtain ⟨b, hb, hb'⟩ := product_supported_one_block hp hq blockLabel blockLabel hsupport
  cases b with
  | none =>
    have hz : ∀ j, p (.inr j) = 0 := fun j => hb _ (by simp [blockLabel])
    have hz' : ∀ j, q (.inr j) = 0 := fun j => hb' _ (by simp [blockLabel])
    obtain ⟨hp', hep⟩ := probability_entropy_inl hp hz
    obtain ⟨hq', heq⟩ := probability_entropy_inl hq hz'
    rw [hp'.2, one_mul, hep, heq]
    have hl := entropy_le_log_card hp'
    have hr := entropy_le_log_card hq'
    simp only [Fintype.card_fin] at hl hr
    linarith
  | some j =>
    have hz : ∀ i, i ≠ Sum.inr j → p i = 0 := by
      intro i hi
      apply hb
      cases i <;> simp_all [blockLabel]
    have hz' : ∀ i, i ≠ Sum.inr j → q i = 0 := by
      intro i hi
      apply hb'
      cases i <;> simp_all [blockLabel]
    rw [entropy_eq_zero_of_single_support hp (.inr j) hz,
      entropy_eq_zero_of_single_support hq (.inr j) hz']
    have hsum : (∑ i : Fin S, p (.inl i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hz _ (by simp)
    simp [hsum]

/-- The exact block-mass probability vector. -/
noncomputable def blockWeights (S r : ℕ) : Option (Fin r) → ℝ
  | none => (S : ℝ)^2 / ((S : ℝ)^2 + r)
  | some _ => 1 / ((S : ℝ)^2 + r)

/-- The entropy formula uses a fixed finite dimension when `r` is fixed. -/
theorem entropy_blockWeights (S r : ℕ) :
    entropy (blockWeights S r) =
      Real.negMulLog ((S : ℝ)^2 / ((S : ℝ)^2 + r)) +
        (r : ℝ) * Real.negMulLog (1 / ((S : ℝ)^2 + r)) := by
  simp [entropy, Fintype.sum_option, blockWeights]

/-- The number of nonzero entries of the block matrix. -/
theorem matrixMass_blockMatrix (S r : ℕ) :
    matrixMass (blockMatrix S r) = (S : ℝ)^2 + r := by
  simp [matrixMass, Fintype.sum_sum_type, pow_two]

theorem matrixMass_blockMatrix_pos (S r : ℕ) (hS : 1 ≤ S) :
    0 < matrixMass (blockMatrix S r) := by
  rw [matrixMass_blockMatrix]
  have hs : 0 < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
  positivity

theorem isProbability_blockWeights (S r : ℕ) (hS : 1 ≤ S) :
    IsProbability (blockWeights S r) := by
  have hm : 0 < (S : ℝ)^2 + r := by
    simpa [matrixMass_blockMatrix] using matrixMass_blockMatrix_pos S r hS
  constructor
  · intro b
    cases b <;> simp only [blockWeights] <;> positivity
  · simp only [Fintype.sum_option, blockWeights, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Entropy of the normalized Boolean block matrix. -/
theorem entropy_normalize_blockMatrix (S r : ℕ) (hS : 1 ≤ S) :
    entropy (Function.uncurry (normalize (blockMatrix S r))) = Real.log ((S : ℝ)^2 + r) := by
  have hbool : ∀ ij : (Fin S ⊕ Fin r) × (Fin S ⊕ Fin r),
      Function.uncurry (blockMatrix S r) ij = 0 ∨
        Function.uncurry (blockMatrix S r) ij = 1 := by
    intro ij
    simp only [Function.uncurry, blockMatrix]
    split_ifs <;> simp
  have hmass : (∑ ij : (Fin S ⊕ Fin r) × (Fin S ⊕ Fin r),
      Function.uncurry (blockMatrix S r) ij) = (S : ℝ)^2 + r := by
    simpa [Fintype.sum_prod_type, Function.uncurry, matrixMass] using matrixMass_blockMatrix S r
  have hm : 0 < (S : ℝ)^2 + r := by
    simpa [matrixMass_blockMatrix] using matrixMass_blockMatrix_pos S r hS
  have h := entropy_normalize_boolean hbool (by rwa [hmass])
  rw [hmass] at h
  change entropy (fun ij : (Fin S ⊕ Fin r) × (Fin S ⊕ Fin r) =>
    blockMatrix S r ij.1 ij.2 / matrixMass (blockMatrix S r)) = _
  rw [matrixMass_blockMatrix]
  exact h

/-- The block-mass entropy equals joint entropy minus within-block entropy. -/
theorem entropy_blockWeights_eq (S r : ℕ) (hS : 1 ≤ S) :
    entropy (blockWeights S r) = Real.log ((S : ℝ)^2 + r) -
      ((S : ℝ)^2 / ((S : ℝ)^2 + r)) * (2 * Real.log S) := by
  have hs : 0 < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hm : (S : ℝ)^2 + r ≠ 0 := ne_of_gt (by positivity)
  rw [entropy_blockWeights]
  simp only [Real.negMulLog]
  rw [Real.log_div (pow_ne_zero 2 hs.ne') hm,
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hm, Real.log_pow]
  simp only [Real.log_one]
  field_simp
  ring

/-- The normalized distribution within an individual block. -/
noncomputable def blockComponent (S r : ℕ) : Option (Fin r) → (Fin S ⊕ Fin r) → ℝ
  | none, .inl _ => 1 / S
  | none, .inr _ => 0
  | some _, .inl _ => 0
  | some j, .inr k => if k = j then 1 else 0

theorem isProbability_blockComponent (S r : ℕ) (hS : 1 ≤ S) (b : Option (Fin r)) :
    IsProbability (blockComponent S r b) := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast (by omega : S ≠ 0)
  constructor
  · intro i
    cases b <;> cases i <;> simp only [blockComponent]
    · positivity
    · norm_num
    · norm_num
    · split_ifs <;> norm_num
  · cases b <;> simp [Fintype.sum_sum_type, blockComponent, hs]

theorem entropy_blockComponent_none (S r : ℕ) (hS : 1 ≤ S) :
    entropy (blockComponent S r none) = Real.log S := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast (by omega : S ≠ 0)
  simp [entropy, Fintype.sum_sum_type, blockComponent, Real.negMulLog, Real.log_inv, hs]

theorem entropy_blockComponent_some (S r : ℕ) (j : Fin r) :
    entropy (blockComponent S r (some j)) = 0 := by
  simp [entropy, Fintype.sum_sum_type, blockComponent, apply_ite Real.negMulLog]

theorem block_reconstruct (S r : ℕ) (hS : 1 ≤ S) (i j : Fin S ⊕ Fin r) :
    normalize (blockMatrix S r) i j = ∑ b,
      blockWeights S r b * blockComponent S r b i * blockComponent S r b j := by
  have hs : (S : ℝ) ≠ 0 := by exact_mod_cast (by omega : S ≠ 0)
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [normalize, matrixMass_blockMatrix, Fintype.sum_option, blockWeights, blockComponent]
      field_simp
    | inr j =>
      simp [normalize, matrixMass_blockMatrix, Fintype.sum_option, blockWeights, blockComponent]
  | inr i =>
    cases j with
    | inl j =>
      simp [normalize, matrixMass_blockMatrix, Fintype.sum_option, blockWeights, blockComponent]
    | inr j =>
      by_cases hij : i = j
      · subst j
        simp [normalize, matrixMass_blockMatrix, Fintype.sum_option, blockWeights, blockComponent]
      · simp [normalize, matrixMass_blockMatrix, Fintype.sum_option, blockWeights, blockComponent,
          hij, mul_ite]

/-- The explicit seed first chooses a block, then samples its two coordinates independently. -/
noncomputable def blockSeed (S r : ℕ) (hS : 1 ≤ S) :
    ProductSeed (normalize (blockMatrix S r)) (Fintype.card (Option (Fin r))) :=
  ProductSeed.ofFintype (blockWeights S r) (blockComponent S r) (blockComponent S r)
    (isProbability_blockWeights S r hS) (isProbability_blockComponent S r hS)
    (isProbability_blockComponent S r hS) (block_reconstruct S r hS)

/-- The block seed attains block-label entropy, rather than merely bounding it. -/
theorem cost_blockSeed (S r : ℕ) (hS : 1 ≤ S) :
    (blockSeed S r hS).cost = entropy (blockWeights S r) := by
  rw [blockSeed, ProductSeed.cost_ofFintype, entropy_normalize_blockMatrix S r hS,
    Fintype.sum_option]
  simp only [entropy_blockComponent_none S r hS, entropy_blockComponent_some,
    add_zero, mul_zero, Finset.sum_const_zero]
  rw [entropy_blockWeights_eq S r hS]
  simp only [blockWeights]
  ring

/-- In every finite seed, the total weight placed in the large block is fixed
by the marginal of the represented matrix. -/
theorem ProductSeed.big_block_mass {S r k : ℕ}
    (s : ProductSeed (normalize (blockMatrix S r)) k) :
    (∑ z, s.weight z * ∑ i : Fin S, s.left z (.inl i)) =
      (S : ℝ)^2 / ((S : ℝ)^2 + r) := by
  calc
    _ = ∑ i : Fin S, ∑ z, s.weight z * s.left z (.inl i) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin S, ∑ j, normalize (blockMatrix S r) (.inl i) j := by
      simp_rw [s.left_marginal]
    _ = _ := by
      simp [normalize, matrixMass_blockMatrix, Fintype.sum_sum_type]
      ring

/-- The sharp lower bound covers every finite seed, not just block-uniform seeds. -/
theorem ProductSeed.block_cost_lower {S r k : ℕ} (hS : 1 ≤ S)
    (s : ProductSeed (normalize (blockMatrix S r)) k) :
    entropy (blockWeights S r) ≤ s.cost := by
  have hcomp : ∀ z, s.weight z * (entropy (s.left z) + entropy (s.right z)) ≤
      s.weight z * ((∑ i : Fin S, s.left z (.inl i)) * (2 * Real.log S)) := by
    intro z
    rcases (s.weight_prob.1 z).eq_or_lt with hz | hz
    · simp [← hz]
    · apply mul_le_mul_of_nonneg_left _ (s.weight_prob.1 z)
      apply product_block_entropy_bound (s.left_prob z) (s.right_prob z)
      intro i j hij
      apply s.zero_of_zero hz
      simp [normalize, blockMatrix, hij]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hcomp z)
  have heq : (∑ z, s.weight z * ((∑ i : Fin S, s.left z (.inl i)) * (2 * Real.log S))) =
      ((S : ℝ)^2 / ((S : ℝ)^2 + r)) * (2 * Real.log S) := by
    simp only [← mul_assoc, ← Finset.sum_mul, s.big_block_mass]
  rw [heq] at hsum
  rw [ProductSeed.cost, entropy_normalize_blockMatrix S r hS, entropy_blockWeights_eq S r hS]
  linarith

/-- Exact common information of the large-block plus singleton family. -/
theorem commonInformationNat_blockMatrix (S r : ℕ) (hS : 1 ≤ S) :
    commonInformationNat (blockMatrix S r) = entropy (blockWeights S r) := by
  apply le_antisymm
  · simpa only [cost_blockSeed] using commonInformationNat_le_cost (blockSeed S r hS)
  · apply le_commonInformationNat (blockMatrix_nonneg S r) (matrixMass_blockMatrix_pos S r hS)
    intro k s
    exact s.block_cost_lower hS

end Lemmata.CommonInformationHsb
