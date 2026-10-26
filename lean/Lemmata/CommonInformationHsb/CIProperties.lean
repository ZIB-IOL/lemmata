module

public import Lemmata.CommonInformationHsb.CommonInformation

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Total matrix mass scales linearly. -/
theorem matrixMass_scale (c : ℝ) (M : I → J → ℝ) :
    matrixMass (fun i j => c * M i j) = c * matrixMass M := by
  simp [matrixMass, Finset.mul_sum]

/-- Global nonzero scaling leaves the normalized matrix unchanged. -/
theorem normalize_scale {c : ℝ} (hc : c ≠ 0) (M : I → J → ℝ) :
    normalize (fun i j => c * M i j) = normalize M := by
  funext i j
  simp only [normalize, matrixMass_scale]
  exact mul_div_mul_left _ _ hc

/-- Common information in nats is invariant under positive global scaling. -/
theorem commonInformationNat_scale {c : ℝ} (hc : 0 < c) (M : I → J → ℝ) :
    commonInformationNat (fun i j => c * M i j) = commonInformationNat M := by
  unfold commonInformationNat admissibleCosts
  rw [normalize_scale hc.ne']

/-- Common information in bits is invariant under positive global scaling. -/
theorem commonInformation_scale {c : ℝ} (hc : 0 < c) (M : I → J → ℝ) :
    commonInformation (fun i j => c * M i j) = commonInformation M := by
  simp only [commonInformation, commonInformationNat_scale hc]

/-- Independent output coordinates need only a single deterministic seed value. -/
noncomputable def ProductSeed.independent {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    ProductSeed (fun i j => p i * q j) 1 where
  weight _ := 1
  left _ := p
  right _ := q
  weight_prob := ⟨fun _ => zero_le_one, by simp⟩
  left_prob _ := hp
  right_prob _ := hq
  reconstruct i j := by simp

/-- The deterministic seed of an independent distribution has zero mutual information. -/
theorem ProductSeed.cost_independent {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    (ProductSeed.independent hp hq).cost = 0 := by
  have he : entropy (Function.uncurry (fun i j => p i * q j)) = entropy p + entropy q :=
    entropy_product hp hq
  simp [ProductSeed.cost, ProductSeed.independent, he]

/-- Genuine finite-seed common information vanishes on independent probability vectors. -/
theorem commonInformationNat_product {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    commonInformationNat (fun i j => p i * q j) = 0 := by
  have hm : matrixMass (fun i j => p i * q j) = 1 := matrixMass_eq_one (hp.prod hq)
  apply le_antisymm _ (commonInformationNat_nonneg
    (fun i j => mul_nonneg (hp.1 i) (hq.1 j)) (by rw [hm]; norm_num))
  let s : ProductSeed (normalize (fun i j => p i * q j)) 1 := {
    weight := fun _ => 1
    left := fun _ => p
    right := fun _ => q
    weight_prob := ⟨fun _ => zero_le_one, by simp⟩
    left_prob := fun _ => hp
    right_prob := fun _ => hq
    reconstruct := fun i j => by simp [normalize, hm] }
  have h := commonInformationNat_le_cost s
  have he : entropy (Function.uncurry (fun i j => p i * q j)) = entropy p + entropy q :=
    entropy_product hp hq
  simpa [s, ProductSeed.cost, normalize_eq_self hm, he] using h

/-- The independent-distribution zero result in bits. -/
theorem commonInformation_product {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    commonInformation (fun i j => p i * q j) = 0 := by
  simp [commonInformation, commonInformationNat_product hp hq]

/-- The total mass of an outer product is the product of the marginal masses. -/
theorem matrixMass_product (u : I → ℝ) (v : J → ℝ) :
    matrixMass (fun i j => u i * v j) = (∑ i, u i) * ∑ j, v j := by
  simp only [matrixMass, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Normalization of an outer product factors into the two vector normalizations. -/
theorem normalize_product (u : I → ℝ) (v : J → ℝ) :
    normalize (fun i j => u i * v j) =
      fun i j => (u i / ∑ a, u a) * (v j / ∑ b, v b) := by
  funext i j
  simp [normalize, matrixMass_product, div_mul_div_comm]

/-- Every nonnegative rank-one outer product of positive mass has zero common information. -/
theorem commonInformationNat_rankOne {u : I → ℝ} {v : J → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hmass : 0 < matrixMass (fun i j => u i * v j)) :
    commonInformationNat (fun i j => u i * v j) = 0 := by
  have hu0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu i)
  have hv0 : 0 ≤ ∑ j, v j := Finset.sum_nonneg (fun j _ => hv j)
  rw [matrixMass_product] at hmass
  have hu1 : 0 < ∑ i, u i := by nlinarith
  have hv1 : 0 < ∑ j, v j := by nlinarith
  have hp := isProbability_div_sum hu hu1
  have hq := isProbability_div_sum hv hv1
  have hm : matrixMass (fun i j => (u i / ∑ a, u a) * (v j / ∑ b, v b)) = 1 :=
    matrixMass_eq_one (hp.prod hq)
  have hn := normalize_eq_self hm
  have he : commonInformationNat (fun i j => u i * v j) =
      commonInformationNat (fun i j => (u i / ∑ a, u a) * (v j / ∑ b, v b)) := by
    unfold commonInformationNat admissibleCosts
    rw [hn, normalize_product]
  rw [he]
  exact commonInformationNat_product hp hq

/-- The nonnegative rank-one zero result in bits. -/
theorem commonInformation_rankOne {u : I → ℝ} {v : J → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hmass : 0 < matrixMass (fun i j => u i * v j)) :
    commonInformation (fun i j => u i * v j) = 0 := by
  simp [commonInformation, commonInformationNat_rankOne hu hv hmass]

end Lemmata.CommonInformationHsb
