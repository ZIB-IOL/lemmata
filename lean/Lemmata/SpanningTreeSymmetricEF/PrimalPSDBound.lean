module

public import Lemmata.SpanningTreeSymmetricEF.IdentitySlack
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section


/-!
# Direct primal nonnegative-outer PSD lower bounds

Actual affine PSD lifts containing a zero/identity coordinate simplex have
order at least its number of non-base points. Arbitrary auxiliary variables,
singular feasible matrices and varying-order product blocks are allowed.
The spanning-tree corollaries use actual tree witnesses from `IdentitySlack`.
All domination arguments concern quadratic forms and Gram rows; no conic
duality, trace-factorization hypothesis or classification of faces is used.
-/

namespace Lemmata.SpanningTreeSymmetricEF.PrimalPSDBound

open Matrix Classical
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The real quadratic form of a matrix. -/
def qform (A : Matrix κ κ ℝ) (x : κ → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

lemma qform_nonneg {A : Matrix κ κ ℝ} (hA : A.PosSemidef) (x : κ → ℝ) :
    0 ≤ qform A x := by
  simpa [qform] using hA.dotProduct_mulVec_nonneg x

lemma qform_gram (U : Matrix κ κ ℝ) (x : κ → ℝ) :
    qform (Uᴴ * U) x = ∑ r, (U r ⬝ᵥ x) ^ 2 := by
  rw [qform, ← Matrix.mulVec_mulVec, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec, pow_two]

/-- Vectors whose squared evaluation is bounded by a fixed nonnegative form.
Submodule closure encodes the finite Cauchy--Schwarz domination argument. -/
def boundedRows (q : (κ → ℝ) → ℝ) : Submodule ℝ (κ → ℝ) where
  carrier := {v | ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (v ⬝ᵥ x) ^ 2 ≤ C * q x}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  add_mem' := by
    rintro u v ⟨C, hC, hu⟩ ⟨D, hD, hv⟩
    refine ⟨2 * (C + D), by positivity, fun x => ?_⟩
    rw [add_dotProduct]
    have := hu x
    have := hv x
    nlinarith [sq_nonneg ((u ⬝ᵥ x) - (v ⬝ᵥ x))]
  smul_mem' := by
    rintro a v ⟨C, hC, hv⟩
    refine ⟨a ^ 2 * C, by positivity, fun x => ?_⟩
    rw [smul_dotProduct, smul_eq_mul, mul_pow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hv x) (sq_nonneg a)

/-- If every Gram row is bounded by a PSD quadratic form, so is its Gram matrix. -/
theorem gram_dominated_of_rows (U : Matrix κ κ ℝ) (B : Matrix κ κ ℝ)
    (hB : B.PosSemidef)
    (hrows : ∀ r, U r ∈ boundedRows (qform B)) :
    ∃ C : ℝ, 0 ≤ C ∧ (C • B - Uᴴ * U).PosSemidef := by
  classical
  choose C hC hbound using hrows
  refine ⟨∑ r, C r, Finset.sum_nonneg (fun r _ => hC r), ?_⟩
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨(hB.smul (Finset.sum_nonneg (fun r _ => hC r))).1.sub
    (Matrix.posSemidef_conjTranspose_mul_self U).1, fun x => ?_⟩
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hbound r x)
  rw [← qform_gram, ← Finset.sum_mul] at h
  simpa [qform, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, sub_nonneg] using h

omit [Fintype ι] [Fintype κ] in
/-- A family of vectors each outside its own submodule, with every other vector
inside that submodule, is linearly independent. -/
theorem independent_of_separating_submodules
    (S : ι → Submodule ℝ (κ → ℝ)) (v : ι → κ → ℝ)
    (hout : ∀ i, v i ∉ S i) (hin : ∀ i j, j ≠ i → v j ∈ S i) :
    LinearIndependent ℝ v := by
  rw [linearIndependent_iff_notMem_span]
  intro i hi
  apply hout i
  apply (Submodule.span_le.mpr ?_) hi
  rintro _ ⟨j, hj, rfl⟩
  exact hin i j (by simpa using hj.2)

lemma qform_sum {τ : Type*} (s : Finset τ) (A : τ → Matrix κ κ ℝ)
    (x : κ → ℝ) : qform (∑ j ∈ s, A j) x = ∑ j ∈ s, qform (A j) x := by
  simp [qform, Matrix.sum_mulVec, dotProduct_sum]

lemma qform_smul (c : ℝ) (A : Matrix κ κ ℝ) (x : κ → ℝ) :
    qform (c • A) x = c * qform A x := by
  simp [qform, Matrix.smul_mulVec, dotProduct_smul]

/-- Sum of all points except a specified non-base point; the baseline is retained. -/
noncomputable def otherSum (A : Option ι → Matrix κ κ ℝ) (i : ι) : Matrix κ κ ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.erase (some i), A j

omit [Fintype κ] in
lemma otherSum_psd (A : Option ι → Matrix κ κ ℝ)
    (hA : ∀ j, (A j).PosSemidef) (i : ι) : (otherSum A i).PosSemidef := by
  classical
  exact Matrix.posSemidef_sum _ (fun j _ => hA j)

/-- Too many non-base PSD matrices force one of them to be dominated by the sum
of the others, including the baseline. This is a primal, order-level statement. -/
theorem exists_dominated_of_card_gt
    (A : Option ι → Matrix κ κ ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ i : ι, ∃ C : ℝ, 0 ≤ C ∧ (C • otherSum A i - A (some i)).PosSemidef := by
  classical
  by_contra h
  have hbad : ∀ i : ι, ¬ ∃ C : ℝ, 0 ≤ C ∧
      (C • otherSum A i - A (some i)).PosSemidef := by
    simpa only [not_exists] using h
  choose U hU using fun j => PSDRank.exists_gram_factor (hA j)
  have hrow : ∀ i : ι, ∃ r : κ,
      U (some i) r ∉ boundedRows (qform (otherSum A i)) := by
    intro i
    by_contra hr
    push Not at hr
    apply hbad i
    simpa only [hU (some i)] using
      gram_dominated_of_rows (U (some i)) (otherSum A i) (otherSum_psd A hA i) hr
  choose r hr using hrow
  have hlin : LinearIndependent ℝ (fun i => U (some i) (r i)) := by
    apply independent_of_separating_submodules
      (fun i => boundedRows (qform (otherSum A i))) _ hr
    intro i j hji
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [one_mul]
    calc
      (U (some j) (r j) ⬝ᵥ x) ^ 2
          ≤ ∑ t, (U (some j) t ⬝ᵥ x) ^ 2 :=
        Finset.single_le_sum (fun t _ => sq_nonneg (U (some j) t ⬝ᵥ x))
          (Finset.mem_univ (r j))
      _ = qform (A (some j)) x := by rw [hU, qform_gram]
      _ ≤ qform (otherSum A i) x := by
        rw [otherSum, qform_sum]
        exact Finset.single_le_sum (fun t _ => qform_nonneg (hA t) x)
          (by simp [hji])
  have hle := hlin.fintype_card_le_finrank
  have hdim : Module.finrank ℝ (κ → ℝ) = Fintype.card κ := Module.finrank_fintype_fun_eq_card ℝ
  rw [hdim] at hle
  omega

section WeightedSum

variable {τ E : Type*} [Fintype τ] [DecidableEq τ]
    [AddCommGroup E] [Module ℝ E]

lemma sum_one_exception (p : τ → E) (i : τ) (a b : ℝ) :
    (∑ j, (if j = i then a else b) • p j) =
      a • p i + b • ∑ j ∈ Finset.univ.erase i, p j := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  rw [add_comm]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_erase] at hj
  simp [hj.1]

end WeightedSum

/-- An affine simplex coefficient system whose PSD pencil forces every non-base
coefficient to be nonnegative needs matrix order at least the number of such
coefficients. This theorem has no factorization or duality input. -/
theorem card_le_of_psd_coefficients
    (A : Option ι → Matrix κ κ ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hcoeff : ∀ w : Option ι → ℝ, (∑ j, w j) = 1 →
      (∑ j, w j • A j).PosSemidef → ∀ i : ι, 0 ≤ w (some i)) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  by_contra hcard
  obtain ⟨i, C, hC, hdom⟩ := exists_dominated_of_card_gt A hA (by omega)
  let d : ℝ := (C + 2) * Fintype.card ι - 1
  have hn : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hd : 0 < d := by dsimp [d]; nlinarith
  let w : Option ι → ℝ := fun j => if j = some i then -1 else C + 2
  have hw : (∑ j, w j) = d := by
    have hh := sum_one_exception (fun _ : Option ι => (1 : ℝ)) (some i) (-1) (C + 2)
    simpa [w, d, Finset.card_erase_of_mem, Fintype.card_option, add_comm, mul_comm,
      sub_eq_add_neg] using hh
  have hpsd : (∑ j, w j • A j).PosSemidef := by
    rw [show (∑ j, w j • A j) = -A (some i) + (C + 2) • otherSum A i from
      by simpa [w, otherSum] using sum_one_exception A (some i) (-1) (C + 2)]
    convert hdom.add ((otherSum_psd A hA i).smul (show (0 : ℝ) ≤ 2 by norm_num)) using 1
    module
  have hsum : (∑ j, d⁻¹ * w j) = 1 := by
    rw [← Finset.mul_sum, hw, inv_mul_cancel₀ hd.ne']
  have hnorm : (∑ j, (d⁻¹ * w j) • A j).PosSemidef := by
    simpa only [Finset.smul_sum, smul_smul] using hpsd.smul (inv_nonneg.mpr hd.le)
  have hneg := hcoeff (fun j => d⁻¹ * w j) hsum hnorm i
  have hinv : 0 < d⁻¹ := inv_pos.mpr hd
  simp only [w, ite_true, mul_neg, mul_one] at hneg
  linarith

section AffineLift

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Direct geometric lower bound. The lift can have arbitrary extra variables:
`E` need not be finite-dimensional. The slice and both maps are actual affine
objects; feasibility implies coordinate nonnegativity, and the displayed
points have the actual zero/identity coordinate pattern. -/
theorem card_le_of_affine_psd_lift
    (S : AffineSubspace ℝ E)
    (pencil : E →ᵃ[ℝ] Matrix κ κ ℝ) (projection : E →ᵃ[ℝ] (ι → ℝ))
    (z : Option ι → E)
    (hz : ∀ j, z j ∈ S) (hpsd : ∀ j, (pencil (z j)).PosSemidef)
    (hcoord : ∀ j i, projection (z j) i = if j = some i then 1 else 0)
    (houter : ∀ x ∈ S, (pencil x).PosSemidef → ∀ i, 0 ≤ projection x i) :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  apply card_le_of_psd_coefficients (fun j => pencil (z j)) hpsd
  intro w hw hmat i
  let x := Finset.univ.affineCombination ℝ z w
  have hx : x ∈ S := by
    have hspan : affineSpan ℝ (Set.range z) ≤ S :=
      affineSpan_le.mpr (by rintro _ ⟨j, rfl⟩; exact hz j)
    exact hspan (affineCombination_mem_affineSpan hw z)
  have hp : pencil x = ∑ j, w j • pencil (z j) := by
    dsimp [x]
    rw [Finset.map_affineCombination _ _ _ hw,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    rfl
  have hy : projection x = ∑ j, w j • projection (z j) := by
    dsimp [x]
    rw [Finset.map_affineCombination _ _ _ hw,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    rfl
  have hyi : projection x i = w (some i) := by
    rw [hy]
    simp [Finset.sum_apply, hcoord, smul_eq_mul]
  rw [← hyi]
  exact houter x hx (hp.symm ▸ hmat) i

/-- Application to actual spanning-tree images of an actual nonnegative-outer
PSD lift. Only the geometric lift equations, feasibility and containment are
inputs; neither trace factors nor conic duality are assumed. -/
theorem tree_order_bound_of_affine_psd_lift
    {V : Type*} [Fintype V]
    (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree)
    (S : AffineSubspace ℝ E)
    (pencil : E →ᵃ[ℝ] Matrix κ κ ℝ)
    (projection : E →ᵃ[ℝ] (IdentitySlack.Nonedge T₀ → ℝ))
    (hcontains : ∀ T : SimpleGraph V, T.IsTree → ∃ z ∈ S,
      (pencil z).PosSemidef ∧ ∀ e, projection z e = IdentitySlack.coordinateSlack e.val T)
    (houter : ∀ z ∈ S, (pencil z).PosSemidef → ∀ e, 0 ≤ projection z e) :
    (Fintype.card V - 1).choose 2 ≤ Fintype.card κ := by
  classical
  obtain ⟨T, hT, hid⟩ := IdentitySlack.exists_identity_slack T₀ hT₀
  obtain ⟨z₀, hz₀, hp₀, hc₀⟩ := hcontains T₀ hT₀
  choose z hz hp hc using fun i => hcontains (T i) (hT i)
  rw [← IdentitySlack.card_nonedge T₀ hT₀]
  apply card_le_of_affine_psd_lift S pencil projection (Option.elim · z₀ z)
  · intro j; cases j with
    | none => exact hz₀
    | some i => exact hz i
  · intro j; cases j with
    | none => exact hp₀
    | some i => exact hp i
  · intro j i
    cases j with
    | none => simpa only [Option.elim_none, reduceCtorEq, ite_false] using
        (hc₀ i).trans (IdentitySlack.coordinateSlack_base T₀ i)
    | some j => simpa only [Option.elim_some, Option.some.injEq, eq_comm] using
        (hc j i).trans (hid i j)
  · exact houter

section Blocks

variable {β : Type*} [Fintype β] {δ : β → Type*} [∀ b, Fintype (δ b)]

/-- The genuine linear block-diagonal embedding for varying matrix orders. -/
noncomputable def blockDiagonalLinear :
    (∀ b, Matrix (δ b) (δ b) ℝ) →ₗ[ℝ] Matrix (Σ b, δ b) (Σ b, δ b) ℝ where
  toFun := Matrix.blockDiagonal'
  map_add' := Matrix.blockDiagonal'_add
  map_smul' := Matrix.blockDiagonal'_smul

/-- Assemble actual affine matrix pencils without adding any constraints. -/
noncomputable def blockPencil (pencil : ∀ b, E →ᵃ[ℝ] Matrix (δ b) (δ b) ℝ) :
    E →ᵃ[ℝ] Matrix (Σ b, δ b) (Σ b, δ b) ℝ :=
  (blockDiagonalLinear (δ := δ)).toAffineMap.comp (AffineMap.pi pencil)

omit [Fintype β] [∀ b, Fintype (δ b)] in
lemma blockPencil_apply (pencil : ∀ b, E →ᵃ[ℝ] Matrix (δ b) (δ b) ℝ) (x : E) :
    blockPencil pencil x = Matrix.blockDiagonal' (fun b => pencil b x) := rfl

/-- PSD of the assembled pencil is exactly feasibility of every block. -/
theorem blockPencil_psd_iff (pencil : ∀ b, E →ᵃ[ℝ] Matrix (δ b) (δ b) ℝ) (x : E) :
    (blockPencil pencil x).PosSemidef ↔ ∀ b, (pencil b x).PosSemidef := by
  constructor
  · intro h b
    have hh := h.submatrix (fun i : δ b => (⟨b, i⟩ : Σ b, δ b))
    have heq : (blockPencil pencil x).submatrix
        (fun i : δ b => (⟨b, i⟩ : Σ b, δ b))
        (fun i : δ b => (⟨b, i⟩ : Σ b, δ b)) = pencil b x := by
      ext i j
      simp only [blockPencil_apply, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_eq]
    exact heq ▸ hh
  · intro h
    exact PSDRank.posSemidef_blockDiagonal (fun b => pencil b x) h

/-- Product-cone version of the geometric lower bound, measuring size by the
sum of the block orders, not the sum of their squares. -/
theorem card_le_sum_of_affine_psd_lift
    (S : AffineSubspace ℝ E)
    (pencil : ∀ b, E →ᵃ[ℝ] Matrix (δ b) (δ b) ℝ)
    (projection : E →ᵃ[ℝ] (ι → ℝ)) (z : Option ι → E)
    (hz : ∀ j, z j ∈ S) (hpsd : ∀ j b, (pencil b (z j)).PosSemidef)
    (hcoord : ∀ j i, projection (z j) i = if j = some i then 1 else 0)
    (houter : ∀ x ∈ S, (∀ b, (pencil b x).PosSemidef) → ∀ i, 0 ≤ projection x i) :
    Fintype.card ι ≤ ∑ b, Fintype.card (δ b) := by
  have h := card_le_of_affine_psd_lift S (blockPencil pencil) projection z hz
    (fun j => (blockPencil_psd_iff pencil (z j)).mpr (hpsd j)) hcoord
    (fun x hx hp => houter x hx ((blockPencil_psd_iff pencil x).mp hp))
  simpa only [Fintype.card_sigma] using h

/-- Full direct primal lower bound for a geometric product-PSD lift containing
all actual spanning-tree images and contained in the nonnegative orthant. -/
theorem tree_sum_order_bound_of_affine_psd_lift
    {V : Type*} [Fintype V]
    (T₀ : SimpleGraph V) (hT₀ : T₀.IsTree)
    (S : AffineSubspace ℝ E)
    (pencil : ∀ b, E →ᵃ[ℝ] Matrix (δ b) (δ b) ℝ)
    (projection : E →ᵃ[ℝ] (IdentitySlack.Nonedge T₀ → ℝ))
    (hcontains : ∀ T : SimpleGraph V, T.IsTree → ∃ z ∈ S,
      (∀ b, (pencil b z).PosSemidef) ∧
        ∀ e, projection z e = IdentitySlack.coordinateSlack e.val T)
    (houter : ∀ z ∈ S, (∀ b, (pencil b z).PosSemidef) → ∀ e, 0 ≤ projection z e) :
    (Fintype.card V - 1).choose 2 ≤ ∑ b, Fintype.card (δ b) := by
  have h := tree_order_bound_of_affine_psd_lift T₀ hT₀ S (blockPencil pencil) projection
    (fun T hT => by
      obtain ⟨z, hz, hp, hc⟩ := hcontains T hT
      exact ⟨z, hz, (blockPencil_psd_iff pencil z).mpr hp, hc⟩)
    (fun z hz hp => houter z hz ((blockPencil_psd_iff pencil z).mp hp))
  simpa only [Fintype.card_sigma] using h

end Blocks
end AffineLift

omit [Fintype ι] in
/-- Regression witness: diagonal PSD pencils realize the required geometric
zero/identity pattern at equality, including the empty coordinate type. -/
theorem diagonal_lift_witness :
    ∃ pencil : (ι → ℝ) →ᵃ[ℝ] Matrix ι ι ℝ,
      (∀ x, (pencil x).PosSemidef ↔ ∀ i, 0 ≤ x i) ∧
      ∃ z : Option ι → ι → ℝ,
        (∀ j, (pencil (z j)).PosSemidef) ∧
        ∀ j i, z j i = if j = some i then 1 else 0 := by
  classical
  refine ⟨(Matrix.diagonalLinearMap ι ℝ ℝ).toAffineMap, ?_,
    (fun j i => if j = some i then 1 else 0), ?_, fun _ _ => rfl⟩
  · intro x
    exact Matrix.posSemidef_diagonal_iff
  · intro j
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ if j = some i then (1 : ℝ) else 0
    split <;> norm_num

/-- Adversarial regression: a zero-order PSD pencil cannot cut out even one
nonnegative non-base coefficient. -/
theorem zero_order_coefficients_impossible
    (A : Option Unit → Matrix (Fin 0) (Fin 0) ℝ)
    (hA : ∀ j, (A j).PosSemidef)
    (hcoeff : ∀ w : Option Unit → ℝ, (∑ j, w j) = 1 →
      (∑ j, w j • A j).PosSemidef → ∀ i : Unit, 0 ≤ w (some i)) : False := by
  have h := card_le_of_psd_coefficients A hA hcoeff
  simp at h

#print axioms exists_dominated_of_card_gt
#print axioms card_le_of_affine_psd_lift
#print axioms tree_order_bound_of_affine_psd_lift
#print axioms tree_sum_order_bound_of_affine_psd_lift
#print axioms diagonal_lift_witness
#print axioms zero_order_coefficients_impossible

end Lemmata.SpanningTreeSymmetricEF.PrimalPSDBound
