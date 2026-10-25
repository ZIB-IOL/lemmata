module

public import Lemmata.CommonInformationHsb.Seeds

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] {k : ℕ}

/-- The marginal probability of the auxiliary value in a finite joint law. -/
noncomputable def jointSeedMass (q : Fin k × (I × J) → ℝ) (z : Fin k) : ℝ :=
  ∑ i, ∑ j, q (z, (i, j))

/-- The joint marginal of the auxiliary value and the left coordinate. -/
noncomputable def jointLeftMass (q : Fin k × (I × J) → ℝ) (z : Fin k) (i : I) : ℝ :=
  ∑ j, q (z, (i, j))

/-- The joint marginal of the auxiliary value and the right coordinate. -/
noncomputable def jointRightMass (q : Fin k × (I × J) → ℝ) (z : Fin k) (j : J) : ℝ :=
  ∑ i, q (z, (i, j))

/-- Conditional independence written without division. At positive seed mass this
is exactly the product condition for the conditional row/column distribution;
zero seed masses impose no extra choice of conditional probabilities. -/
def JointConditionallyIndependent (q : Fin k × (I × J) → ℝ) : Prop :=
  ∀ z i j, q (z, (i, j)) * jointSeedMass q z =
    jointLeftMass q z i * jointRightMass q z j

theorem jointSeedMass_nonneg {q : Fin k × (I × J) → ℝ}
    (hq : IsProbability q) (z : Fin k) : 0 ≤ jointSeedMass q z :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hq.1 (z, (i, j))))

theorem jointSeedMass_probability {q : Fin k × (I × J) → ℝ}
    (hq : IsProbability q) : IsProbability (jointSeedMass q) := by
  refine ⟨jointSeedMass_nonneg hq, ?_⟩
  simpa only [jointSeedMass, Fintype.sum_prod_type] using hq.2

theorem joint_entry_le_seedMass {q : Fin k × (I × J) → ℝ}
    (hq : IsProbability q) (z : Fin k) (i : I) (j : J) :
    q (z, (i, j)) ≤ jointSeedMass q z := by
  exact (Finset.single_le_sum (fun j _ => hq.1 (z, (i, j)))
    (Finset.mem_univ j)).trans (Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hq.1 (z, (i, j))))
      (Finset.mem_univ i))

theorem joint_entry_eq_zero {q : Fin k × (I × J) → ℝ}
    (hq : IsProbability q) {z : Fin k} (hz : jointSeedMass q z = 0) (i : I) (j : J) :
    q (z, (i, j)) = 0 := by
  have h := joint_entry_le_seedMass hq z i j
  rw [hz] at h
  exact le_antisymm h (hq.1 _)

/-- A joint law with the product conditional-independence identity gives an
admissible product seed. Conditional distributions at zero-mass values use point
masses, which do not affect the reconstructed law or information cost. -/
noncomputable def ProductSeed.ofJoint {P : I → J → ℝ}
    (q : Fin k × (I × J) → ℝ) (hq : IsProbability q)
    (hout : ∀ i j, ∑ z, q (z, (i, j)) = P i j)
    (hind : JointConditionallyIndependent q) : ProductSeed P k := by
  classical
  let a : I := (Classical.choice hq.nonempty).2.1
  let b : J := (Classical.choice hq.nonempty).2.2
  let w := jointSeedMass q
  let l : Fin k → I → ℝ := fun z i =>
    if w z = 0 then (if i = a then 1 else 0) else jointLeftMass q z i / w z
  let r : Fin k → J → ℝ := fun z j =>
    if w z = 0 then (if j = b then 1 else 0) else jointRightMass q z j / w z
  refine ⟨w, l, r, jointSeedMass_probability hq, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : w z = 0
    · simpa [l, hz] using isProbability_pointMass a
    · have hsum : ∑ i, jointLeftMass q z i = w z := rfl
      have hs : 0 < ∑ i, jointLeftMass q z i := by
        rw [hsum]
        exact lt_of_le_of_ne (jointSeedMass_nonneg hq z) (Ne.symm hz)
      simpa only [l, ite_eq_right hz, hsum] using
        (isProbability_div_sum (p := jointLeftMass q z)
          (fun i => Finset.sum_nonneg (fun j _ => hq.1 (z, (i, j)))) hs)
  · intro z
    by_cases hz : w z = 0
    · simpa [r, hz] using isProbability_pointMass b
    · have hsum : ∑ j, jointRightMass q z j = w z := by
        simp only [jointRightMass, w, jointSeedMass]
        exact Finset.sum_comm
      have hs : 0 < ∑ j, jointRightMass q z j := by
        rw [hsum]
        exact lt_of_le_of_ne (jointSeedMass_nonneg hq z) (Ne.symm hz)
      have hh := isProbability_div_sum (p := jointRightMass q z)
        (fun j => Finset.sum_nonneg (fun i _ => hq.1 (z, (i, j)))) hs
      simpa only [r, ite_eq_right hz, hsum] using hh
  · intro i j
    rw [← hout i j]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : w z = 0
    · have hzero := joint_entry_eq_zero hq hz i j
      simp only [hz, zero_mul, hzero]
    · dsimp [l, r]
      rw [ite_eq_right hz, ite_eq_right hz]
      have hc := hind z i j
      change q (z, (i, j)) * w z = _ at hc
      calc
        q (z, (i, j)) = (jointLeftMass q z i * jointRightMass q z j) / w z :=
          (eq_div_iff hz).2 hc
        _ = w z * (jointLeftMass q z i / w z) * (jointRightMass q z j / w z) := by
          field_simp
          <;> ring

@[simp] theorem ProductSeed.ofJoint_weight {P : I → J → ℝ}
    (q : Fin k × (I × J) → ℝ) (hq : IsProbability q)
    (hout : ∀ i j, ∑ z, q (z, (i, j)) = P i j)
    (hind : JointConditionallyIndependent q) :
    (ProductSeed.ofJoint q hq hout hind).weight = jointSeedMass q := rfl

/-- The reverse construction preserves the full joint distribution, not only
its output marginal. -/
theorem ProductSeed.joint_ofJoint {P : I → J → ℝ}
    (q : Fin k × (I × J) → ℝ) (hq : IsProbability q)
    (hout : ∀ i j, ∑ z, q (z, (i, j)) = P i j)
    (hind : JointConditionallyIndependent q) :
    (ProductSeed.ofJoint q hq hout hind).joint = q := by
  classical
  funext x
  rcases x with ⟨z, i, j⟩
  by_cases hz : jointSeedMass q z = 0
  · simp [ProductSeed.joint, ProductSeed.ofJoint, hz, joint_entry_eq_zero hq hz i j]
  · simp only [ProductSeed.joint, ProductSeed.ofJoint, ite_eq_right hz]
    have hc := hind z i j
    field_simp
    nlinarith

/-- Every product seed satisfies the standard finite conditional-independence
identity for its actual joint law. -/
theorem ProductSeed.joint_conditionallyIndependent {P : I → J → ℝ}
    (s : ProductSeed P k) : JointConditionallyIndependent s.joint := by
  intro z i j
  have hw : jointSeedMass s.joint z = s.weight z := by
    simpa only [jointSeedMass, Fintype.sum_prod_type] using s.joint_seed z
  have hl : jointLeftMass s.joint z i = s.weight z * s.left z i := by
    simp [jointLeftMass, ProductSeed.joint, ← mul_assoc, ← Finset.mul_sum,
      (s.right_prob z).2]
  have hr : jointRightMass s.joint z j = s.weight z * s.right z j := by
    simp only [jointRightMass, ProductSeed.joint, ← Finset.mul_sum, ← Finset.sum_mul,
      (s.left_prob z).2, one_mul]
  rw [hw, hl, hr]
  simp only [ProductSeed.joint]
  ring

/-- Product-mixture seeds represent exactly the conditionally independent finite
joint laws, with no restriction to uniform rectangle components. -/
theorem joint_conditionallyIndependent_iff {P : I → J → ℝ}
    (q : Fin k × (I × J) → ℝ) (hq : IsProbability q)
    (hout : ∀ i j, ∑ z, q (z, (i, j)) = P i j) :
    JointConditionallyIndependent q ↔ ∃ s : ProductSeed P k, s.joint = q := by
  constructor
  · intro hind
    exact ⟨ProductSeed.ofJoint q hq hout hind, ProductSeed.joint_ofJoint q hq hout hind⟩
  · rintro ⟨s, rfl⟩
    exact s.joint_conditionallyIndependent

/-- The information objective of a general finite independent seed is preserved
by the conversion to product mixtures. -/
theorem ProductSeed.cost_ofJoint {P : I → J → ℝ}
    (q : Fin k × (I × J) → ℝ) (hq : IsProbability q)
    (hout : ∀ i j, ∑ z, q (z, (i, j)) = P i j)
    (hind : JointConditionallyIndependent q) :
    (ProductSeed.ofJoint q hq hout hind).cost =
      entropy (Function.uncurry P) + entropy (jointSeedMass q) - entropy q := by
  rw [ProductSeed.cost_eq_mutualInformation, ProductSeed.joint_ofJoint,
    ProductSeed.ofJoint_weight]

end Lemmata.CommonInformationHsb
