module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- A finite probability vector, allowing zero coordinates. -/
def IsProbability (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Finite Shannon entropy, in natural-log units, with `0 log 0 = 0`. -/
noncomputable def entropy (p : I → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- Total mass of a finite real matrix. -/
noncomputable def matrixMass (M : I → J → ℝ) : ℝ := ∑ i, ∑ j, M i j

/-- Divide every matrix entry by its total mass. -/
noncomputable def normalize (M : I → J → ℝ) (i : I) (j : J) : ℝ :=
  M i j / matrixMass M

namespace IsProbability

variable {p : I → ℝ}

theorem nonneg (hp : IsProbability p) (i : I) : 0 ≤ p i := hp.1 i

theorem sum_eq_one (hp : IsProbability p) : ∑ i, p i = 1 := hp.2

theorem le_one (hp : IsProbability p) (i : I) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

theorem nonempty (hp : IsProbability p) : Nonempty I := by
  by_contra h
  have : IsEmpty I := not_nonempty_iff.mp h
  simpa using hp.2

theorem prod {q : J → ℝ} (hp : IsProbability p) (hq : IsProbability q) :
    IsProbability (fun ij : I × J => p ij.1 * q ij.2) := by
  constructor
  · intro ij
    exact mul_nonneg (hp.1 _) (hq.1 _)
  · simp [Fintype.sum_prod_type, ← Finset.mul_sum, hp.2, hq.2]

theorem mixture {w : K → ℝ} {q : K → I → ℝ}
    (hw : IsProbability w) (hq : ∀ z, IsProbability (q z)) :
    IsProbability (fun i => ∑ z, w z * q z i) := by
  constructor
  · intro i
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hw.1 z) ((hq z).1 i))
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (hq _).2, mul_one]
    exact hw.2

end IsProbability

/-- Entropy is nonnegative for every finite probability vector. -/
theorem entropy_nonneg {p : I → ℝ} (hp : IsProbability p) : 0 ≤ entropy p :=
  Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hp.1 i) (hp.le_one i))

theorem matrixMass_nonneg {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ matrixMass M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hM i j))

theorem matrixMass_pos {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hne : ∃ i j, M i j ≠ 0) : 0 < matrixMass M := by
  obtain ⟨i, j, hij⟩ := hne
  have hentry : 0 < M i j := lt_of_le_of_ne (hM i j) (Ne.symm hij)
  exact hentry.trans_le ((Finset.single_le_sum (fun j _ => hM i j)
    (Finset.mem_univ j)).trans (Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hM i j)) (Finset.mem_univ i)))

theorem matrixMass_eq_one {M : I → J → ℝ}
    (hM : IsProbability (Function.uncurry M)) : matrixMass M = 1 := by
  simpa [matrixMass, Fintype.sum_prod_type, Function.uncurry] using hM.2

theorem normalize_nonneg {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (i : I) (j : J) : 0 ≤ normalize M i j :=
  div_nonneg (hM i j) (matrixMass_nonneg hM)

theorem matrixMass_normalize {M : I → J → ℝ} (hmass : matrixMass M ≠ 0) :
    matrixMass (normalize M) = 1 := by
  simp only [matrixMass, normalize, div_eq_mul_inv, ← Finset.sum_mul]
  exact div_self hmass

theorem isProbability_normalize {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hmass : 0 < matrixMass M) : IsProbability (Function.uncurry (normalize M)) := by
  constructor
  · intro ij
    exact normalize_nonneg hM ij.1 ij.2
  · simpa [matrixMass, Fintype.sum_prod_type, Function.uncurry] using
      matrixMass_normalize hmass.ne'

theorem normalize_eq_self {M : I → J → ℝ} (hmass : matrixMass M = 1) :
    normalize M = M := by
  funext i j
  simp [normalize, hmass]

/-- The scaling identity does not require positive scalars or positive entries. -/
theorem entropy_mul (c : ℝ) (p : I → ℝ) :
    entropy (fun i => c * p i) = (∑ i, p i) * Real.negMulLog c + c * entropy p := by
  simp [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]

/-- Chain rule for a joint distribution specified by weights and conditional probabilities. -/
theorem entropy_joint (w : K → ℝ) {q : K → I → ℝ}
    (hq : ∀ z, IsProbability (q z)) :
    entropy (fun zi : K × I => w zi.1 * q zi.1 zi.2) =
      entropy w + ∑ z, w z * entropy (q z) := by
  simp only [entropy, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, (hq _).2, one_mul]

/-- Entropy of independent coordinates is additive. -/
theorem entropy_product {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    entropy (fun ij : I × J => p ij.1 * q ij.2) = entropy p + entropy q := by
  rw [entropy_joint p (fun _ => hq), ← Finset.sum_mul, hp.2, one_mul]

theorem entropy_prod {p : I → ℝ} {q : J → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) :
    entropy (fun ij : I × J => p ij.1 * q ij.2) = entropy p + entropy q :=
  entropy_product hp hq

/-- Finite concavity of entropy; zero weights and zero coordinates are permitted. -/
theorem entropy_le_mixture {w : K → ℝ} {q : K → I → ℝ}
    (hw : IsProbability w) (hq : ∀ z, IsProbability (q z)) :
    ∑ z, w z * entropy (q z) ≤ entropy (fun i => ∑ z, w z * q z i) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  exact Real.concaveOn_negMulLog.le_map_sum (fun z _ => hw.1 z) hw.2
    (fun z _ => (hq z).1 i)

/-- Normalization of a finite nonnegative vector of positive mass. -/
theorem isProbability_div_sum {p : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : 0 < ∑ i, p i) : IsProbability (fun i => p i / ∑ j, p j) := by
  constructor
  · intro i
    exact div_nonneg (hp i) hs.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hs.ne'

/-- A point mass is a probability distribution. -/
theorem isProbability_pointMass [DecidableEq I] (a : I) :
    IsProbability (fun i => if i = a then 1 else 0) := by
  constructor
  · intro i
    dsimp only
    split_ifs <;> norm_num
  · simp

/-- A point mass has zero entropy. -/
theorem entropy_pointMass [DecidableEq I] (a : I) :
    entropy (fun i => if i = a then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  split_ifs <;> simp

/-- The uniform probability vector on a nonempty finite type. -/
theorem isProbability_uniform [Nonempty I] :
    IsProbability (fun _ : I => (Fintype.card I : ℝ)⁻¹) := by
  constructor
  · intro i
    positivity
  · simp [Fintype.card_ne_zero]

/-- Uniform entropy is the natural logarithm of the size of the type. -/
theorem entropy_uniform [Nonempty I] :
    entropy (fun _ : I => (Fintype.card I : ℝ)⁻¹) = Real.log (Fintype.card I) := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [entropy, Real.negMulLog, Real.log_inv, hn]

/-- The entropy of a finite probability vector is at most log of its alphabet size. -/
theorem entropy_le_log_card {p : I → ℝ} (hp : IsProbability p) :
    entropy p ≤ Real.log (Fintype.card I) := by
  have : Nonempty I := hp.nonempty
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hu := isProbability_uniform (I := I)
  have h := Real.concaveOn_negMulLog.le_map_sum
    (fun i (_ : i ∈ (Finset.univ : Finset I)) => hu.1 i) hu.2
    (fun i (_ : i ∈ (Finset.univ : Finset I)) => hp.1 i)
  change ∑ i, (Fintype.card I : ℝ)⁻¹ * Real.negMulLog (p i) ≤
    Real.negMulLog (∑ i, (Fintype.card I : ℝ)⁻¹ * p i) at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, hp.2, mul_one] at h
  have h' := mul_le_mul_of_nonneg_left h hn.le
  simpa [entropy, Real.negMulLog, Real.log_inv, ← mul_assoc, hn.ne'] using h'

/-- Subadditivity of `-x log x` on nonnegative finite sums. -/
theorem negMulLog_sum_le (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Real.negMulLog (∑ i, p i) ≤ ∑ i, Real.negMulLog (p i) := by
  by_cases hs : ∑ i, p i = 0
  · have hz : ∀ i, p i = 0 := by
      intro i
      apply le_antisymm _ (hp i)
      calc
        p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
        _ = 0 := hs
    simp [hz]
  · have hspos : 0 < ∑ i, p i := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => hp i)) (Ne.symm hs)
    have hprob := isProbability_div_sum hp hspos
    have hid := entropy_mul (∑ i, p i) (fun i => p i / ∑ j, p j)
    have heq : (fun i => (∑ j, p j) * (p i / ∑ j, p j)) = p := by
      funext i
      exact mul_div_cancel₀ _ hs
    rw [heq, hprob.2, one_mul] at hid
    have hnon := mul_nonneg hspos.le (entropy_nonneg hprob)
    change Real.negMulLog (∑ i, p i) ≤ entropy p
    linarith

/-- Mixing cannot increase entropy beyond the weight entropy plus the average entropy. -/
theorem entropy_mixture_le {w : K → ℝ} {q : K → I → ℝ}
    (hw : IsProbability w) (hq : ∀ z, IsProbability (q z)) :
    entropy (fun i => ∑ z, w z * q z i) ≤ entropy w + ∑ z, w z * entropy (q z) := by
  calc
    entropy (fun i => ∑ z, w z * q z i) ≤ ∑ i, ∑ z, Real.negMulLog (w z * q z i) :=
      Finset.sum_le_sum (fun i _ => negMulLog_sum_le _
        (fun z => mul_nonneg (hw.1 z) ((hq z).1 i)))
    _ = entropy (fun zi : K × I => w zi.1 * q zi.1 zi.2) := by
      rw [Finset.sum_comm]
      simp [entropy, Fintype.sum_prod_type]
    _ = entropy w + ∑ z, w z * entropy (q z) := entropy_joint w hq

/-- Restriction to any finite set containing the support preserves probability. -/
theorem IsProbability.restrict {p : I → ℝ} (hp : IsProbability p)
    (s : Finset I) (hs : ∀ i, i ∉ s → p i = 0) :
    IsProbability (fun i : s => p i) := by
  classical
  constructor
  · intro i
    exact hp.1 i
  · rw [← Finset.sum_subtype s (fun _ => Iff.rfl)]
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hs i hi)]
    exact hp.2

/-- Entropy is unchanged by restricting to a finite set containing its support. -/
theorem entropy_restrict (p : I → ℝ) (s : Finset I)
    (hs : ∀ i, i ∉ s → p i = 0) : entropy (fun i : s => p i) = entropy p := by
  classical
  unfold entropy
  rw [← Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => Real.negMulLog (p i))]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hs i hi])

/-- The entropy cap using any finite set containing the support. -/
theorem entropy_le_log_card_of_support {p : I → ℝ} (hp : IsProbability p)
    (s : Finset I) (hs : ∀ i, i ∉ s → p i = 0) :
    entropy p ≤ Real.log s.card := by
  have h := entropy_le_log_card (hp.restrict s hs)
  simpa [Fintype.card_coe, entropy_restrict p s hs] using h

/-- The entropy cap using exactly the nonzero support. -/
theorem entropy_le_log_card_support [DecidableEq I] {p : I → ℝ}
    [DecidablePred (fun i => p i ≠ 0)] (hp : IsProbability p) :
    entropy p ≤ Real.log ((Finset.univ.filter fun i => p i ≠ 0).card) := by
  apply entropy_le_log_card_of_support hp
  intro i hi
  simpa using hi

/-- Entropy is invariant under relabelling by an equivalence. -/
theorem entropy_equiv (e : I ≃ J) (p : J → ℝ) :
    entropy (fun i => p (e i)) = entropy p :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- A Boolean-valued vector has zero unnormalized entropy. -/
theorem entropy_boolean {p : I → ℝ} (hp : ∀ i, p i = 0 ∨ p i = 1) :
    entropy p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rcases hp i with hi | hi <;> simp [hi]

/-- Normalizing a nonzero Boolean vector gives entropy log of its mass. -/
theorem entropy_normalize_boolean {p : I → ℝ} (hp : ∀ i, p i = 0 ∨ p i = 1)
    (hs : 0 < ∑ i, p i) :
    entropy (fun i => p i / ∑ j, p j) = Real.log (∑ i, p i) := by
  simp_rw [div_eq_mul_inv, mul_comm (p _)]
  rw [entropy_mul, entropy_boolean hp]
  simp [Real.negMulLog, Real.log_inv, hs.ne']

/-- Finite entropy is continuous, including at vectors with zero coordinates. -/
theorem continuous_entropy : Continuous (entropy (I := I)) := by
  unfold entropy
  fun_prop

end Lemmata.CommonInformationHsb
