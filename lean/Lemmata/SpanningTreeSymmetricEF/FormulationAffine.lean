module

public import Lemmata.SpanningTreeSymmetricEF.FormulationTransport
public import Lemmata.SpanningTreeSymmetricEF.SignedLift

@[expose] public section


/-! Literal affine lifts and coherent vertex actions for the concrete upper formulations. -/
namespace Lemmata.SpanningTreeSymmetricEF.FormulationAffine
open scoped BigOperators
open SDPBounds TreeModels ApproximationUpper FormulationStructure
noncomputable section
variable {V : Type}

abbrev Mat (V : Type*) := Matrix V V ℝ
abbrev Pair (V : Type*) := Mat V × Mat V

def matrixLinearEquiv (g : Equiv.Perm V) : Mat V ≃ₗ[ℝ] Mat V where
  toFun := permuteMatrix g
  invFun := permuteMatrix g.symm
  left_inv M := by ext i j; simp [permuteMatrix]
  right_inv M := by ext i j; simp [permuteMatrix]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A genuine group homomorphism, with composition in the inverse-reindex convention. -/
def matrixAction : Equiv.Perm V →* (Mat V ≃ᵃ[ℝ] Mat V) where
  toFun g := (matrixLinearEquiv g).toAffineEquiv
  map_one' := by ext M i j; rfl
  map_mul' g h := by ext M i j; rfl

def pairAction : Equiv.Perm V →* (Pair V ≃ᵃ[ℝ] Pair V) where
  toFun g := (matrixAction g).prodCongr (matrixAction g)
  map_one' := by ext z <;> rfl
  map_mul' g h := by ext z <;> rfl

def projectionLinear : Mat V →ₗ[ℝ] (Sym2 V → ℝ) where
  toFun := projection
  map_add' y z := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => simp [projection, edgeWeights]; ring
  map_smul' a y := by
    funext e
    induction e using Sym2.inductionOn with
    | _ i j => simp [projection, edgeWeights]; ring

@[simp] theorem projectionLinear_apply (y : Mat V) : projectionLinear y = projection y := rfl

def projectionAffine : Mat V →ᵃ[ℝ] (Sym2 V → ℝ) := projectionLinear.toAffineMap

def pairProjectionAffine : Pair V →ᵃ[ℝ] (Sym2 V → ℝ) :=
  projectionAffine.comp (LinearMap.fst ℝ (Mat V) (Mat V)).toAffineMap

theorem projection_equivariant (g : Equiv.Perm V) (y : Mat V) :
    projectionAffine (matrixAction g y) = permuteVector g (projectionAffine y) :=
  projection_permute g y

theorem pairProjection_equivariant (g : Equiv.Perm V) (z : Pair V) :
    pairProjectionAffine (pairAction g z) = permuteVector g (pairProjectionAffine z) :=
  projection_permute g z.1

variable [Fintype V]

def rowLinear (i : V) : Mat V →ₗ[ℝ] ℝ := ∑ j, Matrix.entryLinearMap ℝ ℝ i j

def edgeLinear (e : Sym2 V) : Mat V →ₗ[ℝ] ℝ :=
  (LinearMap.proj e).comp projectionLinear

def lpSlackAffine : ScalarConstraint V → Mat V →ᵃ[ℝ] ℝ
  | .inl p => (Matrix.entryLinearMap ℝ ℝ p.val.1 p.val.2).toAffineMap
  | .inr (.inl e) => AffineMap.const ℝ _ 1 - (edgeLinear e.val).toAffineMap
  | .inr (.inr i) => AffineMap.const ℝ _ 1 - (rowLinear i).toAffineMap

@[simp] theorem lpSlackAffine_apply (q : ScalarConstraint V) (y : Mat V) :
    lpSlackAffine q y = lpSlack y q := by
  rcases q with p | e | i <;> simp [lpSlackAffine, lpSlack, edgeLinear, rowLinear,
    projectionLinear]

/-- Symmetrization makes this affine on all matrices, not only symmetric ones. -/
def cutAffine (e : Sym2 V) : Mat V →ᵃ[ℝ] ℝ :=
  (1 / 4 : ℝ) • (AffineMap.const ℝ _ 2 - (edgeLinear e).toAffineMap)

omit [Fintype V] in
@[simp] theorem cutAffine_apply (e : Sym2 V) (X : Mat V) :
    cutAffine e X = cutProjection X e := by
  induction e using Sym2.inductionOn with
  | _ i j => simp [cutAffine, cutProjection, edgeLinear, projectionLinear,
      projection, edgeWeights]; ring

def sdpSlackAffine : ScalarConstraint V → Pair V →ᵃ[ℝ] ℝ
  | .inl p => (lpSlackAffine (.inl p)).comp (LinearMap.fst ℝ (Mat V) (Mat V)).toAffineMap
  | .inr (.inl e) =>
      (cutAffine e.val).comp (LinearMap.snd ℝ (Mat V) (Mat V)).toAffineMap -
      (edgeLinear e.val).toAffineMap.comp (LinearMap.fst ℝ (Mat V) (Mat V)).toAffineMap
  | .inr (.inr i) =>
      (lpSlackAffine (.inr (.inr i))).comp (LinearMap.fst ℝ (Mat V) (Mat V)).toAffineMap

@[simp] theorem sdpSlackAffine_apply (q : ScalarConstraint V) (z : Pair V) :
    sdpSlackAffine q z = sdpSlack z.1 z.2 q := by
  rcases q with p | e | i <;> simp [sdpSlackAffine, sdpSlack, lpSlack, edgeLinear,
    projectionLinear]

def lpSlice : AffineSubspace ℝ (Mat V) :=
  (affineSpan ℝ ({0} : Set (V → ℝ))).comap (Matrix.diagLinearMap V ℝ ℝ).toAffineMap

def sdpSlice : AffineSubspace ℝ (Pair V) :=
  lpSlice.comap (LinearMap.fst ℝ (Mat V) (Mat V)).toAffineMap ⊓
  (affineSpan ℝ ({fun _ : V => (1 : ℝ)} : Set (V → ℝ))).comap
    ((Matrix.diagLinearMap V ℝ ℝ).comp (LinearMap.snd ℝ (Mat V) (Mat V))).toAffineMap

omit [Fintype V] in
@[simp] theorem mem_lpSlice (y : Mat V) : y ∈ lpSlice ↔ ∀ i, y i i = 0 := by
  simp [lpSlice, funext_iff, Matrix.diag]

omit [Fintype V] in
@[simp] theorem mem_sdpSlice (z : Pair V) :
    z ∈ sdpSlice ↔ (∀ i, z.1 i i = 0) ∧ (∀ i, z.2 i i = 1) := by
  simp [sdpSlice, AffineSubspace.mem_inf_iff, funext_iff, Matrix.diag]

variable [DecidableEq V]

theorem lpImage_eq : SignedLift.lpImage (lpSlice (V := V)) lpSlackAffine projectionAffine =
    lpRelaxation := by
  ext x
  constructor
  · rintro ⟨y, hy, hs, hp⟩
    exact ⟨y, (lp_indexed_constraints y).mpr ⟨(mem_lpSlice y).mp hy,
      fun q => by simpa using hs q⟩, hp⟩
  · rintro ⟨y, hy, hp⟩
    obtain ⟨hd, hs⟩ := (lp_indexed_constraints y).mp hy
    exact ⟨y, (mem_lpSlice y).mpr hd, fun q => by simpa using hs q, hp⟩

abbrev Block (V : Type*) := Unit ⊕ ScalarConstraint V

def Coord : Block V → Type
  | .inl _ => V
  | .inr _ => Unit

instance coordFintype (b : Block V) : Fintype (Coord b) := by
  cases b <;> dsimp [Coord] <;> infer_instance

/-- Order-one matrix embedding of a scalar inequality. -/
def scalarMatrixLinear : ℝ →ₗ[ℝ] Matrix Unit Unit ℝ where
  toFun a := fun _ _ => a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def psdBlockAffine : (b : Block V) → Pair V →ᵃ[ℝ] Matrix (Coord b) (Coord b) ℝ
  | .inl _ => (LinearMap.snd ℝ (Mat V) (Mat V)).toAffineMap
  | .inr q => scalarMatrixLinear.toAffineMap.comp (sdpSlackAffine q)

theorem scalarMatrix_posSemidef (a : ℝ) : (scalarMatrixLinear a).PosSemidef ↔ 0 ≤ a := by
  have heq : scalarMatrixLinear a = Matrix.diagonal (fun _ : Unit => a) := by
    ext i j; cases i; cases j; rfl
  rw [heq, Matrix.posSemidef_diagonal_iff]
  simp

omit [DecidableEq V] in
theorem blocks_posSemidef (z : Pair V) :
    (∀ b, (psdBlockAffine b z).PosSemidef) ↔
      z.2.PosSemidef ∧ ∀ q, 0 ≤ sdpSlack z.1 z.2 q := by
  constructor
  · intro h
    refine ⟨h (.inl ()), fun q => ?_⟩
    have hh := (scalarMatrix_posSemidef _).mp (h (.inr q))
    simpa using hh
  · rintro ⟨hX, hs⟩ (u | q)
    · exact hX
    · exact (scalarMatrix_posSemidef _).mpr (by simpa using hs q)

theorem psdImage_eq : SignedLift.psdImage (sdpSlice (V := V)) psdBlockAffine
    pairProjectionAffine = sdpRelaxation := by
  ext x
  constructor
  · rintro ⟨⟨y, X⟩, hz, hb, hp⟩
    obtain ⟨hd, hdX⟩ := (mem_sdpSlice _).mp hz
    obtain ⟨hX, hs⟩ := (blocks_posSemidef _).mp hb
    exact ⟨y, X, (sdp_indexed_constraints y X).mpr ⟨hd, hX, hdX, hs⟩, hp⟩
  · rintro ⟨y, X, hy, hp⟩
    obtain ⟨hd, hX, hdX, hs⟩ := (sdp_indexed_constraints y X).mp hy
    exact ⟨(y, X), (mem_sdpSlice _).mpr ⟨hd, hdX⟩,
      (blocks_posSemidef _).mpr ⟨hX, hs⟩, hp⟩

/-- The sum of the actual matrix block orders, not a surrogate size parameter. -/
theorem total_block_order : (∑ b : Block V, Fintype.card (Coord b)) =
    3 * (Fintype.card V).choose 2 + 2 * Fintype.card V := by
  rw [Fintype.sum_sum_type]
  change (∑ _ : Unit, Fintype.card V) + (∑ _ : ScalarConstraint V, Fintype.card Unit) = _
  simp only [Fintype.card_unit, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.cast_id]
  rw [scalar_constraint_count]
  omega

omit [DecidableEq V] in
theorem lpAction_feasible (g : Equiv.Perm V) (y : Mat V) :
    LPFeasible (matrixAction g y) ↔ LPFeasible y :=
  FormulationTransport.lp_reindex_iff g y

omit [DecidableEq V] in
theorem sdpAction_feasible (g : Equiv.Perm V) (z : Pair V) :
    Feasible (pairAction g z).1 (pairAction g z).2 ↔ Feasible z.1 z.2 :=
  FormulationTransport.sdp_reindex_iff g z.1 z.2

/-- Literal permutations of the indexed scalar inequalities. -/
def arcEquiv (g : Equiv.Perm V) : Arc V ≃ Arc V where
  toFun p := ⟨(g p.val.1, g p.val.2), g.injective.ne p.property⟩
  invFun p := ⟨(g.symm p.val.1, g.symm p.val.2), g.symm.injective.ne p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def edgeEquiv (g : Equiv.Perm V) : FormulationStructure.Edge V ≃ FormulationStructure.Edge V where
  toFun e := ⟨e.val.map g, fun h => e.property ((Sym2.isDiag_map g.injective).mp h)⟩
  invFun e := ⟨e.val.map g.symm, fun h => e.property ((Sym2.isDiag_map g.symm.injective).mp h)⟩
  left_inv e := by
    apply Subtype.ext
    exact (FormulationTransport.sym2Equiv g).left_inv e.val
  right_inv e := by
    apply Subtype.ext
    exact (FormulationTransport.sym2Equiv g).right_inv e.val

def constraintEquiv (g : Equiv.Perm V) : Equiv.Perm (ScalarConstraint V) :=
  Equiv.sumCongr (arcEquiv g) (Equiv.sumCongr (edgeEquiv g) g)

def constraintAction : Equiv.Perm V →* Equiv.Perm (ScalarConstraint V) where
  toFun := constraintEquiv
  map_one' := by
    ext q
    rcases q with p | ⟨e, he⟩ | i
    · rfl
    · induction e using Sym2.inductionOn with | _ a b => rfl
    · rfl
  map_mul' g h := by
    ext q
    rcases q with p | ⟨e, he⟩ | i
    · rfl
    · induction e using Sym2.inductionOn with | _ a b => rfl
    · rfl

omit [DecidableEq V] in
theorem lpSlack_equivariant (g : Equiv.Perm V) (q : ScalarConstraint V) (y : Mat V) :
    lpSlackAffine (constraintEquiv g q) (matrixAction g y) = lpSlackAffine q y := by
  rcases q with p | ⟨e, he⟩ | i
  · change y (g.symm (g p.val.1)) (g.symm (g p.val.2)) = y p.val.1 p.val.2
    simp
  · induction e using Sym2.inductionOn with
    | _ a b =>
      change 1 - (y (g.symm (g a)) (g.symm (g b)) +
        y (g.symm (g b)) (g.symm (g a))) = 1 - (y a b + y b a)
      simp
  · simp only [lpSlackAffine_apply]
    change 1 - (∑ j, y (g.symm (g i)) (g.symm j)) = 1 - ∑ j, y i j
    simpa using congrArg (fun t : ℝ => 1 - t) (g.symm.sum_comp (fun j => y i j))

omit [DecidableEq V] in
theorem sdpSlack_equivariant (g : Equiv.Perm V) (q : ScalarConstraint V) (z : Pair V) :
    sdpSlackAffine (constraintEquiv g q) (pairAction g z) = sdpSlackAffine q z := by
  rcases q with p | ⟨e, he⟩ | i
  · exact lpSlack_equivariant g (.inl p) z.1
  · induction e using Sym2.inductionOn with
    | _ a b =>
      change (1 / 4 : ℝ) * (2 - (z.2 (g.symm (g a)) (g.symm (g b)) +
        z.2 (g.symm (g b)) (g.symm (g a)))) -
        (z.1 (g.symm (g a)) (g.symm (g b)) + z.1 (g.symm (g b)) (g.symm (g a))) =
        (1 / 4 : ℝ) * (2 - (z.2 a b + z.2 b a)) - (z.1 a b + z.1 b a)
      simp
  · exact lpSlack_equivariant g (.inr (.inr i)) z.1

def blockEquiv (g : Equiv.Perm V) : Equiv.Perm (Block V) :=
  Equiv.sumCongr (Equiv.refl Unit) (constraintEquiv g)

def blockAction : Equiv.Perm V →* Equiv.Perm (Block V) where
  toFun := blockEquiv
  map_one' := by
    ext b
    rcases b with u | q
    · rfl
    · exact congrArg Sum.inr (Equiv.congr_fun constraintAction.map_one q)
  map_mul' g h := by
    ext b
    rcases b with u | q
    · rfl
    · exact congrArg Sum.inr (Equiv.congr_fun (constraintAction.map_mul g h) q)

def blockCoordinateEquiv (g : Equiv.Perm V) : (b : Block V) → Coord b ≃ Coord (blockEquiv g b)
  | .inl _ => g
  | .inr _ => Equiv.refl Unit

omit [DecidableEq V] in
/-- Full coordinate-permutation covariance of the actual affine PSD pencils:
the order-|V| block is reindexed by g; order-one blocks are literally permuted. -/
theorem block_equivariant (g : Equiv.Perm V) (b : Block V) (z : Pair V)
    (i j : Coord (blockEquiv g b)) :
    psdBlockAffine (blockEquiv g b) (pairAction g z) i j =
      psdBlockAffine b z ((blockCoordinateEquiv g b).symm i)
        ((blockCoordinateEquiv g b).symm j) := by
  rcases b with u | q
  · rfl
  · exact sdpSlack_equivariant g q z

end
end Lemmata.SpanningTreeSymmetricEF.FormulationAffine
