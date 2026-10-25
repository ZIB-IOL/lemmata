module

public import Lemmata.CommonInformationHsb.Entropy

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- A finite product-mixture representation. All finite cardinalities are permitted;
zero weights are permitted, and their marginal distributions are still normalized. -/
structure ProductSeed (P : I → J → ℝ) (k : ℕ) where
  weight : Fin k → ℝ
  left : Fin k → I → ℝ
  right : Fin k → J → ℝ
  weight_prob : IsProbability weight
  left_prob : ∀ z, IsProbability (left z)
  right_prob : ∀ z, IsProbability (right z)
  reconstruct : ∀ i j, P i j = ∑ z, weight z * left z i * right z j

/-- Mutual information between the output pair and the mixture seed, in nats. -/
noncomputable def ProductSeed.cost {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) : ℝ :=
  entropy (Function.uncurry P) -
    ∑ z, s.weight z * (entropy (s.left z) + entropy (s.right z))

/-- Construct a seed using any finite indexing type, not just `Fin k`. -/
noncomputable def ProductSeed.ofFintype {P : I → J → ℝ}
    (w : K → ℝ) (l : K → I → ℝ) (r : K → J → ℝ)
    (hw : IsProbability w) (hl : ∀ z, IsProbability (l z))
    (hr : ∀ z, IsProbability (r z))
    (hP : ∀ i j, P i j = ∑ z, w z * l z i * r z j) :
    ProductSeed P (Fintype.card K) where
  weight z := w ((Fintype.equivFin K).symm z)
  left z := l ((Fintype.equivFin K).symm z)
  right z := r ((Fintype.equivFin K).symm z)
  weight_prob := ⟨fun z => hw.1 _, by rw [(Fintype.equivFin K).symm.sum_comp]; exact hw.2⟩
  left_prob z := hl _
  right_prob z := hr _
  reconstruct i j := by
    rw [(Fintype.equivFin K).symm.sum_comp (fun z => w z * l z i * r z j)]
    exact hP i j

theorem ProductSeed.cost_ofFintype {P : I → J → ℝ}
    (w : K → ℝ) (l : K → I → ℝ) (r : K → J → ℝ)
    (hw : IsProbability w) (hl : ∀ z, IsProbability (l z))
    (hr : ∀ z, IsProbability (r z))
    (hP : ∀ i j, P i j = ∑ z, w z * l z i * r z j) :
    (ProductSeed.ofFintype w l r hw hl hr hP).cost =
      entropy (Function.uncurry P) - ∑ z, w z * (entropy (l z) + entropy (r z)) := by
  unfold ProductSeed.cost ProductSeed.ofFintype
  rw [(Fintype.equivFin K).symm.sum_comp (fun z => w z * (entropy (l z) + entropy (r z)))]

theorem ProductSeed.term_le_reconstruct {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) (z : Fin k) (i : I) (j : J) :
    s.weight z * s.left z i * s.right z j ≤ P i j := by
  rw [s.reconstruct]
  exact Finset.single_le_sum (fun t _ =>
    mul_nonneg (mul_nonneg (s.weight_prob.1 t) ((s.left_prob t).1 i))
      ((s.right_prob t).1 j)) (Finset.mem_univ z)

theorem ProductSeed.zero_of_zero {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) {z : Fin k} (hz : 0 < s.weight z)
    {i : I} {j : J} (hP : P i j = 0) : s.left z i * s.right z j = 0 := by
  have h := s.term_le_reconstruct z i j
  rw [hP, mul_assoc] at h
  have hn := mul_nonneg ((s.left_prob z).1 i) ((s.right_prob z).1 j)
  nlinarith

/-- The actual joint distribution of the finite seed and the output pair. -/
noncomputable def ProductSeed.joint {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) (zxy : Fin k × (I × J)) : ℝ :=
  s.weight zxy.1 * (s.left zxy.1 zxy.2.1 * s.right zxy.1 zxy.2.2)

theorem ProductSeed.joint_output {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) (i : I) (j : J) :
    ∑ z, s.joint (z, (i, j)) = P i j := by
  simpa [ProductSeed.joint, mul_assoc] using (s.reconstruct i j).symm

theorem ProductSeed.joint_seed {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) (z : Fin k) :
    ∑ xy : I × J, s.joint (z, xy) = s.weight z := by
  simp only [ProductSeed.joint, Fintype.sum_prod_type, ← Finset.mul_sum]
  simp only [(s.right_prob z).2, mul_one, (s.left_prob z).2]

theorem ProductSeed.joint_probability {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) : IsProbability s.joint := by
  refine ⟨fun x => mul_nonneg (s.weight_prob.1 _) (mul_nonneg
    ((s.left_prob _).1 _) ((s.right_prob _).1 _)), ?_⟩
  rw [Fintype.sum_prod_type]
  simpa only [s.joint_seed] using s.weight_prob.2

/-- Conditional independence, including a precise normalization condition for conditioning. -/
theorem ProductSeed.conditional_product {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) {z : Fin k} (hz : s.weight z ≠ 0) (i : I) (j : J) :
    s.joint (z, (i, j)) / s.weight z = s.left z i * s.right z j := by
  exact mul_div_cancel_left₀ _ hz

theorem ProductSeed.left_marginal {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) (i : I) :
    ∑ j, P i j = ∑ z, s.weight z * s.left z i := by
  simp_rw [s.reconstruct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (s.right_prob _).2, mul_one]

/-- The entropy formula for the seed is exactly ordinary mutual information. -/
theorem ProductSeed.cost_eq_mutualInformation {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) :
    s.cost = entropy (Function.uncurry P) + entropy s.weight - entropy s.joint := by
  have h := entropy_joint s.weight (fun z => (s.left_prob z).prod (s.right_prob z))
  simp_rw [entropy_product (s.left_prob _) (s.right_prob _)] at h
  change entropy s.joint = _ at h
  rw [h, ProductSeed.cost]
  ring

theorem ProductSeed.cost_nonneg {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) : 0 ≤ s.cost := by
  have h := entropy_le_mixture s.weight_prob
    (fun z => (s.left_prob z).prod (s.right_prob z))
  simp_rw [entropy_product (s.left_prob _) (s.right_prob _)] at h
  have he : (fun ij : I × J => ∑ z, s.weight z * (s.left z ij.1 * s.right z ij.2)) =
      Function.uncurry P := by
    funext ij
    simpa only [mul_assoc, Function.uncurry] using (s.reconstruct ij.1 ij.2).symm
  rw [he] at h
  exact sub_nonneg.mpr h

theorem ProductSeed.cost_le_entropy_weight {P : I → J → ℝ} {k : ℕ}
    (s : ProductSeed P k) : s.cost ≤ entropy s.weight := by
  have h := entropy_mixture_le s.weight_prob
    (fun z => (s.left_prob z).prod (s.right_prob z))
  simp_rw [entropy_product (s.left_prob _) (s.right_prob _)] at h
  have he : (fun ij : I × J => ∑ z, s.weight z * (s.left z ij.1 * s.right z ij.2)) =
      Function.uncurry P := by
    funext ij
    simpa only [mul_assoc, Function.uncurry] using (s.reconstruct ij.1 ij.2).symm
  rw [he] at h
  unfold ProductSeed.cost
  linarith

/-- Point masses represent every finite joint probability distribution. -/
noncomputable def ProductSeed.points {P : I → J → ℝ}
    (hP : IsProbability (Function.uncurry P)) : ProductSeed P (Fintype.card (I × J)) := by
  classical
  refine ProductSeed.ofFintype (Function.uncurry P)
    (fun ij i => if i = ij.1 then 1 else 0)
    (fun ij j => if j = ij.2 then 1 else 0) hP ?_ ?_ ?_
  · intro ij
    exact ⟨fun i => by dsimp; split_ifs <;> norm_num, by simp⟩
  · intro ij
    exact ⟨fun j => by dsimp; split_ifs <;> norm_num, by simp⟩
  · intro i j
    simp [Fintype.sum_prod_type, mul_ite]

theorem ProductSeed.cost_points {P : I → J → ℝ}
    (hP : IsProbability (Function.uncurry P)) :
    (ProductSeed.points hP).cost = entropy (Function.uncurry P) := by
  classical
  simp [ProductSeed.points, ProductSeed.cost, ProductSeed.ofFintype, entropy, apply_ite]

end Lemmata.CommonInformationHsb
