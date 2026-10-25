module

public import Lemmata.CommonInformationHsb.Families
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section

namespace Lemmata.CommonInformationHsb

open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J]

/-- Maximum entry, with zero adjoined to handle empty matrices. On nonnegative
nonempty matrices this is the ordinary maximum entry. -/
def maxEntry (M : I → J → ℝ) : ℝ :=
  ↑((Finset.univ : Finset (I × J)).sup (fun ij => (M ij.1 ij.2).toNNReal))

/-- Real witnesses are constrained on every Boolean rectangle, including empty ones.
Negative witness entries are allowed and essential. -/
def RectangleFeasible (W : I → J → ℝ) : Prop :=
  ∀ (A : Finset I) (B : Finset J), ∑ i ∈ A, ∑ j ∈ B, W i j ≤ 1

/-- Entrywise real pairing. -/
def pairing (W M : I → J → ℝ) : ℝ := ∑ i, ∑ j, W i j * M i j

/-- Standard hyperplane separation bound, normalized by the maximum matrix entry. -/
def hsb (M : I → J → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ W : I → J → ℝ, RectangleFeasible W ∧ v = pairing W M / maxEntry M}

theorem maxEntry_nonneg (M : I → J → ℝ) : 0 ≤ maxEntry M := NNReal.coe_nonneg _

theorem le_maxEntry (M : I → J → ℝ) (i : I) (j : J) : M i j ≤ maxEntry M :=
  (Real.le_coe_toNNReal _).trans <| NNReal.coe_le_coe.mpr <|
    Finset.le_sup (f := fun ij : I × J => (M ij.1 ij.2).toNNReal)
      (Finset.mem_univ (i, j))

theorem maxEntry_le {M : I → J → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ i j, M i j ≤ a) : maxEntry M ≤ a := by
  rw [← Real.coe_toNNReal a ha]
  exact NNReal.coe_le_coe.mpr <| Finset.sup_le fun ij _ =>
    Real.toNNReal_le_toNNReal (hM ij.1 ij.2)

theorem maxEntry_eq {M : I → J → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ i j, M i j ≤ a) (i : I) (j : J) (hij : M i j = a) :
    maxEntry M = a :=
  le_antisymm (maxEntry_le ha hM) (hij ▸ le_maxEntry M i j)

theorem maxEntry_pos {M : I → J → ℝ} (hM : ∃ i j, 0 < M i j) :
    0 < maxEntry M := by
  obtain ⟨i, j, hij⟩ := hM
  exact hij.trans_le (le_maxEntry M i j)

omit [Fintype I] [Fintype J] in
theorem rectangleFeasible_zero : RectangleFeasible (fun (_ : I) (_ : J) => 0) := by
  intro A B
  simp

omit [Fintype I] [Fintype J] in
theorem RectangleFeasible.entry_le_one {W : I → J → ℝ} (hW : RectangleFeasible W)
    (i : I) (j : J) : W i j ≤ 1 := by
  simpa using hW {i} {j}

theorem pairing_le_mass {M W : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hW : RectangleFeasible W) : pairing W M ≤ ∑ i, ∑ j, M i j := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa using mul_le_mul_of_nonneg_right (hW.entry_le_one i j) (hM i j)

theorem hsb_objectives_nonempty (M : I → J → ℝ) :
    {v : ℝ | ∃ W, RectangleFeasible W ∧ v = pairing W M / maxEntry M}.Nonempty := by
  refine ⟨0, (fun _ _ => 0), rectangleFeasible_zero, ?_⟩
  simp [pairing]

theorem hsb_objectives_bddAbove {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    BddAbove {v : ℝ | ∃ W, RectangleFeasible W ∧ v = pairing W M / maxEntry M} := by
  refine ⟨(∑ i, ∑ j, M i j) / maxEntry M, ?_⟩
  rintro v ⟨W, hW, rfl⟩
  exact div_le_div_of_nonneg_right (pairing_le_mass hM hW) (maxEntry_nonneg M)

theorem le_hsb_of_witness {M W : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hW : RectangleFeasible W) : pairing W M / maxEntry M ≤ hsb M :=
  le_csSup (hsb_objectives_bddAbove hM) ⟨W, hW, rfl⟩

theorem hsb_le_of_witness_bound {M : I → J → ℝ} {a : ℝ}
    (h : ∀ W, RectangleFeasible W → pairing W M / maxEntry M ≤ a) : hsb M ≤ a := by
  apply csSup_le (hsb_objectives_nonempty M)
  rintro v ⟨W, hW, rfl⟩
  exact h W hW

theorem hsb_nonneg {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) : 0 ≤ hsb M := by
  simpa [pairing] using le_hsb_of_witness hM (rectangleFeasible_zero (I := I) (J := J))

theorem hsb_le_mass_div_maxEntry {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    hsb M ≤ (∑ i, ∑ j, M i j) / maxEntry M := by
  apply hsb_le_of_witness_bound
  intro W hW
  exact div_le_div_of_nonneg_right (pairing_le_mass hM hW) (maxEntry_nonneg M)

theorem hsb_zero : hsb (fun (_ : I) (_ : J) => (0 : ℝ)) = 0 := by
  apply le_antisymm
  · simpa using hsb_le_mass_div_maxEntry (M := fun (_ : I) (_ : J) => (0 : ℝ)) (by simp)
  · exact hsb_nonneg (by simp)

/-- Indicator matrix of a Boolean rectangle. -/
def rectangleMatrix [DecidableEq I] [DecidableEq J] (A : Finset I) (B : Finset J)
    (i : I) (j : J) : ℝ := if i ∈ A ∧ j ∈ B then 1 else 0

theorem pairing_rectangleMatrix [DecidableEq I] [DecidableEq J]
    (W : I → J → ℝ) (A : Finset I) (B : Finset J) :
    pairing W (rectangleMatrix A B) = ∑ i ∈ A, ∑ j ∈ B, W i j := by
  simp [pairing, rectangleMatrix, Finset.sum_ite_irrel, Finset.sum_ite_mem,
    ite_and, mul_ite]

/-- Any weighted Boolean-rectangle decomposition gives an upper certificate. -/
theorem hsb_le_weighted_rectangles [Fintype K] [DecidableEq I] [DecidableEq J]
    {M : I → J → ℝ} (c : K → ℝ) (A : K → Finset I) (B : K → Finset J)
    (hc : ∀ k, 0 ≤ c k)
    (hM : ∀ i j, M i j = ∑ k, c k * rectangleMatrix (A k) (B k) i j) :
    hsb M ≤ (∑ k, c k) / maxEntry M := by
  apply hsb_le_of_witness_bound
  intro W hW
  apply div_le_div_of_nonneg_right _ (maxEntry_nonneg M)
  calc
    pairing W M = ∑ k, c k * pairing W (rectangleMatrix (A k) (B k)) := by
      simp only [pairing, hM, Finset.mul_sum, ← mul_assoc]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ k, c k * 1 := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (by rw [pairing_rectangleMatrix]; exact hW _ _) (hc k)
    _ = ∑ k, c k := by simp

/-- In particular, a sum of `k` unit rectangles bounds HSB by `k / maxEntry`. -/
theorem hsb_le_unit_rectangles [Fintype K] [DecidableEq I] [DecidableEq J]
    {M : I → J → ℝ} (A : K → Finset I) (B : K → Finset J)
    (hM : ∀ i j, M i j = ∑ k, rectangleMatrix (A k) (B k) i j) :
    hsb M ≤ (Fintype.card K : ℝ) / maxEntry M := by
  simpa using hsb_le_weighted_rectangles (fun _ : K => (1 : ℝ)) A B
    (by simp) (by simpa using hM)

/-- The signed identity witness: `+1` on the diagonal, `-1` off it. -/
def identityWitness [DecidableEq I] (i j : I) : ℝ := if i = j then 1 else -1

omit [Fintype I] in
theorem identityWitness_rectangle_sum [DecidableEq I] (A B : Finset I) :
    (∑ i ∈ A, ∑ j ∈ B, identityWitness i j) =
      2 * ((A ∩ B).card : ℝ) - (A.card : ℝ) * (B.card : ℝ) := by
  have hw (i j : I) : identityWitness i j = 2 * (if i = j then (1 : ℝ) else 0) - 1 := by
    by_cases h : i = j <;> norm_num [identityWitness, h]
  simp_rw [hw, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_ite_mem, mul_comm, nsmul_eq_mul]

omit [Fintype I] in
theorem rectangleFeasible_identityWitness [DecidableEq I] :
    RectangleFeasible (identityWitness (I := I)) := by
  intro A B
  rw [identityWitness_rectangle_sum]
  have ha : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hb : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have hc : 2 * (A ∩ B).card ≤ A.card * B.card + 1 := by
    by_cases h : (A ∩ B).card ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
      · simp [h]
      · nlinarith [Nat.mul_le_mul ha hb]
    · have hc2 : 2 ≤ (A ∩ B).card := by omega
      nlinarith [Nat.mul_le_mul ha hb, Nat.mul_le_mul_left (A ∩ B).card hc2]
  have hc' : (2 : ℝ) * (A ∩ B).card ≤ (A.card : ℝ) * B.card + 1 := by exact_mod_cast hc
  linarith

theorem pairing_diagonalMatrix [DecidableEq I] (W : I → I → ℝ) (p : I → ℝ) :
    pairing W (diagonalMatrix p) = ∑ i, W i i * p i := by
  simp [pairing, diagonalMatrix, mul_ite]

/-- The matrix normalizer of a diagonal is exactly the largest nonnegative diagonal weight. -/
theorem maxEntry_diagonalMatrix [DecidableEq I] (p : I → ℝ) :
    maxEntry (diagonalMatrix p) =
      ((Finset.univ.sup (fun i => (p i).toNNReal) : NNReal) : ℝ) := by
  apply le_antisymm
  · apply maxEntry_le (NNReal.coe_nonneg _)
    intro i j
    by_cases hij : i = j
    · simp only [diagonalMatrix, ite_eq_left hij]
      exact (Real.le_coe_toNNReal _).trans <| NNReal.coe_le_coe.mpr <|
        Finset.le_sup (f := fun i => (p i).toNNReal) (Finset.mem_univ i)
    · simp [diagonalMatrix, hij]
  · apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro i _
    apply Real.toNNReal_le_iff_le_coe.mpr
    simpa only [diagonalMatrix_self, maxEntry] using le_maxEntry (diagonalMatrix p) i i

/-- The diagonal formula includes zero weights and even the zero matrix. -/
theorem hsb_diagonalMatrix [DecidableEq I] {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) :
    hsb (diagonalMatrix p) = (∑ i, p i) / maxEntry (diagonalMatrix p) := by
  apply le_antisymm
  · simpa [diagonalMatrix] using hsb_le_mass_div_maxEntry (diagonalMatrix_nonneg hp)
  · simpa [pairing_diagonalMatrix, identityWitness] using
      le_hsb_of_witness (diagonalMatrix_nonneg hp) (rectangleFeasible_identityWitness (I := I))

theorem maxEntry_heavyDiagonal (N : ℕ) (hN : 1 ≤ N) :
    maxEntry (heavyDiagonal N) = 1 / 2 := by
  apply maxEntry_eq (by norm_num) _ none none (by simp [heavyDiagonal, heavyProbability])
  intro i j
  unfold heavyDiagonal diagonalMatrix
  split_ifs
  · cases i with
    | none => simp [heavyProbability]
    | some i =>
      have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
      dsimp [heavyProbability]
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith
  · norm_num

theorem sum_heavyProbability (N : ℕ) (hN : 1 ≤ N) : ∑ i, heavyProbability N i = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp [Fintype.sum_option, heavyProbability]
  field_simp
  ring

/-- The heavy diagonal family has constant HSB equal to two. -/
theorem hsb_heavyDiagonal (N : ℕ) (hN : 1 ≤ N) : hsb (heavyDiagonal N) = 2 := by
  rw [heavyDiagonal, hsb_diagonalMatrix (heavyProbability_nonneg N),
    ← heavyDiagonal, maxEntry_heavyDiagonal N hN, sum_heavyProbability N hN]
  norm_num

/-- Keep the signed identity witness only on a selected set of coordinates. -/
def restrictedIdentityWitness [DecidableEq I] (R : Finset I) (i j : I) : ℝ :=
  if i ∈ R ∧ j ∈ R then identityWitness i j else 0

omit [Fintype I] in
theorem restrictedIdentityWitness_rectangle_sum [DecidableEq I] (R A B : Finset I) :
    (∑ i ∈ A, ∑ j ∈ B, restrictedIdentityWitness R i j) =
      ∑ i ∈ A ∩ R, ∑ j ∈ B ∩ R, identityWitness i j := by
  simp [restrictedIdentityWitness, ite_and, Finset.sum_ite_irrel]

omit [Fintype I] in
theorem rectangleFeasible_restrictedIdentityWitness [DecidableEq I] (R : Finset I) :
    RectangleFeasible (restrictedIdentityWitness R) := by
  intro A B
  rw [restrictedIdentityWitness_rectangle_sum]
  exact rectangleFeasible_identityWitness _ _

theorem pairing_restrictedIdentityWitness [DecidableEq I] (R : Finset I) (M : I → I → ℝ) :
    pairing (restrictedIdentityWitness R) M =
      ∑ i ∈ R, ∑ j ∈ R, identityWitness i j * M i j := by
  simp [pairing, restrictedIdentityWitness, ite_and, ite_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_mem]

/-- A Boolean matrix whose ones are exactly pairs with the same label. -/
def labelBlockMatrix [DecidableEq K] (label : I → K) (i j : I) : ℝ :=
  if label i = label j then 1 else 0

theorem labelBlockMatrix_rectangles [Fintype K] [DecidableEq I] [DecidableEq K]
    (label : I → K) (i j : I) :
    labelBlockMatrix label i j = ∑ k,
      rectangleMatrix (Finset.univ.filter (fun i => label i = k))
        (Finset.univ.filter (fun j => label j = k)) i j := by
  simp [labelBlockMatrix, rectangleMatrix, ite_and, eq_comm]

/-- Exact HSB for label blocks. The section `rep` explicitly supplies a coordinate
in each block; no nonemptiness or support assumption is implicit. -/
theorem hsb_labelBlockMatrix [Fintype K] [DecidableEq I] [DecidableEq K] [Nonempty K]
    (label : I → K) (rep : K → I) (hrep : ∀ k, label (rep k) = k) :
    hsb (labelBlockMatrix label) = (Fintype.card K : ℝ) := by
  have hinj : Function.Injective rep := by
    intro k l h
    simpa only [hrep] using congrArg label h
  have hnonneg : ∀ i j, 0 ≤ labelBlockMatrix label i j := by
    intro i j
    unfold labelBlockMatrix
    split_ifs <;> norm_num
  have hmax : maxEntry (labelBlockMatrix label) = 1 := by
    let k : K := Classical.choice inferInstance
    apply maxEntry_eq zero_le_one _ (rep k) (rep k) (by simp [labelBlockMatrix])
    intro i j
    unfold labelBlockMatrix
    split_ifs <;> norm_num
  apply le_antisymm
  · have hu := hsb_le_unit_rectangles
      (fun k => Finset.univ.filter (fun i => label i = k))
      (fun k => Finset.univ.filter (fun i => label i = k))
      (labelBlockMatrix_rectangles label)
    simpa only [hmax, div_one] using hu
  · let R : Finset I := Finset.univ.image rep
    have hpair : pairing (restrictedIdentityWitness R) (labelBlockMatrix label) =
        (Fintype.card K : ℝ) := by
      rw [pairing_restrictedIdentityWitness]
      simp only [R, Finset.sum_image, hinj.injOn]
      simp [identityWitness, labelBlockMatrix, hrep, hinj.eq_iff, mul_ite]
    have hl := le_hsb_of_witness hnonneg (rectangleFeasible_restrictedIdentityWitness R)
    simpa only [hpair, hmax, div_one] using hl

/-- One chosen element of the large block, and the sole element of each singleton. -/
def blockRepresentative (S r : ℕ) (hS : 1 ≤ S) : Option (Fin r) → Fin S ⊕ Fin r
  | none => .inl ⟨0, by omega⟩
  | some k => .inr k

theorem blockLabel_representative (S r : ℕ) (hS : 1 ≤ S) (k : Option (Fin r)) :
    blockLabel (blockRepresentative S r hS k) = k := by
  cases k <;> rfl

/-- There are precisely `r + 1` nonempty blocks, irrespective of the large block's size. -/
theorem hsb_blockMatrix (S r : ℕ) (hS : 1 ≤ S) :
    hsb (blockMatrix S r) = (r : ℝ) + 1 := by
  change hsb (labelBlockMatrix (@blockLabel S r)) = (r : ℝ) + 1
  simpa using
    hsb_labelBlockMatrix blockLabel (blockRepresentative S r hS)
      (blockLabel_representative S r hS)

/-- On the intended domain, the normalizer really is an attained matrix entry. -/
theorem maxEntry_attained {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hpos : ∃ i j, 0 < M i j) : ∃ i j, maxEntry M = M i j := by
  obtain ⟨i, j, _⟩ := hpos
  obtain ⟨ij, _, hij⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (I × J))
    ⟨(i, j), Finset.mem_univ _⟩ (fun ij => (M ij.1 ij.2).toNNReal)
  refine ⟨ij.1, ij.2, ?_⟩
  simp only [maxEntry, hij, Real.coe_toNNReal _ (hM _ _)]

omit [Fintype I] [Fintype J] in
theorem rectangleFeasible_singleton [DecidableEq I] [DecidableEq J] (i : I) (j : J) :
    RectangleFeasible (rectangleMatrix {i} {j}) := by
  intro A B
  simp only [rectangleMatrix, Finset.mem_singleton, ite_and]
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ B <;> simp [hi, hj]

theorem pairing_singleton [DecidableEq I] [DecidableEq J]
    (M : I → J → ℝ) (i : I) (j : J) : pairing (rectangleMatrix {i} {j}) M = M i j := by
  simp [pairing, rectangleMatrix, ite_and, ite_mul]

/-- Every nonzero nonnegative finite matrix has HSB at least one. -/
theorem one_le_hsb {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hpos : ∃ i j, 0 < M i j) : 1 ≤ hsb M := by
  classical
  obtain ⟨i, j, hij⟩ := maxEntry_attained hM hpos
  have hl := le_hsb_of_witness hM (rectangleFeasible_singleton i j)
  rw [pairing_singleton, ← hij, div_self (ne_of_gt (maxEntry_pos hpos))] at hl
  exact hl

/-- Elementary well-defined bounds, with no linear-programming duality assumption. -/
theorem hsb_bounds {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hpos : ∃ i j, 0 < M i j) :
    1 ≤ hsb M ∧ hsb M ≤ (∑ i, ∑ j, M i j) / maxEntry M :=
  ⟨one_le_hsb hM hpos, hsb_le_mass_div_maxEntry hM⟩

/-- Multiplying a nonzero nonnegative matrix by a positive scalar multiplies its
normalizer by exactly the same scalar. -/
theorem maxEntry_scale {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hpos : ∃ i j, 0 < M i j) (c : ℝ) (hc : 0 < c) :
    maxEntry (fun i j => c * M i j) = c * maxEntry M := by
  obtain ⟨i, j, hij⟩ := maxEntry_attained hM hpos
  refine maxEntry_eq (mul_nonneg hc.le (maxEntry_nonneg M))
    (fun i j => mul_le_mul_of_nonneg_left (le_maxEntry M i j) hc.le) i j ?_
  rw [hij]

/-- The normalized HSB is invariant under positive scaling. -/
theorem hsb_scale {M : I → J → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hpos : ∃ i j, 0 < M i j) (c : ℝ) (hc : 0 < c) :
    hsb (fun i j => c * M i j) = hsb M := by
  have hpair (W : I → J → ℝ) : pairing W (fun i j => c * M i j) = c * pairing W M := by
    simp only [pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hsb, hpair, maxEntry_scale hM hpos c hc, mul_div_mul_left _ _ hc.ne']

end Lemmata.CommonInformationHsb
