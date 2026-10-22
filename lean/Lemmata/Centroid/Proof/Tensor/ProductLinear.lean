module

public import Lemmata.Centroid.Proof.Centroid
public import Lemmata.Centroid.Proof.Linear.TensorSubspaces
public import Mathlib.Data.Matrix.Basis

@[expose] public section

open scoped BigOperators TensorProduct
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F : Type*} [Field F]

def functionProductEquiv {α β : Type*} [Fintype β] :
    (α → F) ⊗[F] (β → F) ≃ₗ[F] (α × β → F) := by
  classical
  exact (TensorProduct.piScalarRight F F (α → F) β).trans
    { toFun := fun f p => f p.2 p.1
      invFun := fun f y x => f (x, y)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem functionProductEquiv_tmul {α β : Type*} [Fintype β]
    (u : α → F) (v : β → F) (p : α × β) :
    functionProductEquiv (u ⊗ₜ[F] v) p = u p.1 * v p.2 := by
  classical
  simp [functionProductEquiv, TensorProduct.piScalarRightHom_tmul,
    smul_eq_mul, mul_comm]

variable {ι : Type*} [Fintype ι]
variable {V W : ι → Type*} [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

def coordinatePairEquiv : (∀ i, V i × W i) ≃ (∀ i, V i) × (∀ i, W i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient-array realization of the abstract tensor product. -/
def productEquiv : (Tensor F ι V) ⊗[F] (Tensor F ι W) ≃ₗ[F]
    Tensor F ι (fun i => V i × W i) := by
  classical
  exact functionProductEquiv.trans (LinearEquiv.funCongrLeft F F coordinatePairEquiv)

omit [∀ i, Fintype (V i)] in
@[simp] theorem productEquiv_tmul (T : Tensor F ι V) (S : Tensor F ι W) :
    productEquiv (T ⊗ₜ[F] S) = kronecker T S := by
  ext x
  simp [productEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
    coordinatePairEquiv, kronecker]

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
private theorem update_pair_fst (x : ∀ i, V i × W i) (i : ι) (a : V i) (b : W i) :
    (fun j => (Function.update x i (a, b) j).1) =
      Function.update (fun j => (x j).1) i a := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
private theorem update_pair_snd (x : ∀ i, V i × W i) (i : ι) (a : V i) (b : W i) :
    (fun j => (Function.update x i (a, b) j).2) =
      Function.update (fun j => (x j).2) i b := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] in
theorem contraction_kronecker (T : Tensor F ι V) (S : Tensor F ι W)
    (i : ι) (u : V i → F) (v : W i → F) :
    contraction (kronecker T S) i (functionProductEquiv (u ⊗ₜ[F] v)) =
      kronecker (contraction T i u) (contraction S i v) := by
  classical
  ext x
  simp only [contraction_apply, functionProductEquiv_tmul, kronecker_apply,
    Fintype.sum_prod_type, update_pair_fst, update_pair_snd]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem concise_kronecker {T : Tensor F ι V} {S : Tensor F ι W}
    (hT : Concise T) (hS : Concise S) : Concise (kronecker T S) := by
  intro i
  have heq : (contraction (kronecker T S) i).comp functionProductEquiv.toLinearMap =
      productEquiv.toLinearMap.comp (TensorProduct.map (contraction T i) (contraction S i)) := by
    apply TensorProduct.ext'
    intro u v
    simpa using contraction_kronecker T S i u v
  have hinj : Function.Injective
      (productEquiv.toLinearMap.comp (TensorProduct.map (contraction T i) (contraction S i))) :=
    productEquiv.injective.comp (TensorProduct.map_injective_of_flat_flat _ _ (hT i) (hS i))
  rw [← heq] at hinj
  intro u v huv
  obtain ⟨a, rfl⟩ := functionProductEquiv.surjective u
  obtain ⟨b, rfl⟩ := functionProductEquiv.surjective v
  exact congrArg functionProductEquiv (hinj huv)

def productMatrix (i : ι) (A : Matrix (V i) (V i) F) (B : Matrix (W i) (W i) F) :
    Matrix (V i × W i) (V i × W i) F := fun x y => A x.1 y.1 * B x.2 y.2

omit [Fintype ι] in
theorem legAction_kronecker (T : Tensor F ι V) (S : Tensor F ι W) (i : ι)
    (A : Matrix (V i) (V i) F) (B : Matrix (W i) (W i) F) :
    legAction (kronecker T S) i (productMatrix i A B) =
      kronecker (legAction T i A) (legAction S i B) := by
  classical
  ext x
  simp only [legAction_apply, productMatrix, kronecker_apply,
    Fintype.sum_prod_type, update_pair_fst, update_pair_snd]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem productMatrix_single (i : ι) (a b : V i) (c d : W i) (z : F) :
    productMatrix i (Matrix.single a b z) (Matrix.single c d (1 : F)) =
      Matrix.single (a, c) (b, d) z := by
  classical
  ext ⟨x, x'⟩ ⟨y, y'⟩
  simp [productMatrix, Matrix.single_apply, Prod.mk.injEq, ite_and]
  split_ifs <;> simp_all

/-- Single-leg action spaces multiply under the coefficient tensor-product equivalence. -/
theorem actionSpace_kronecker (T : Tensor F ι V) (S : Tensor F ι W) (i : ι) :
    actionSpace (kronecker T S) i =
      (Lemmata.Centroid.Linear.tensorSubspace (actionSpace T i) (actionSpace S i)).map
        productEquiv.toLinearMap := by
  classical
  let Q := (Lemmata.Centroid.Linear.tensorSubspace (actionSpace T i) (actionSpace S i)).map
    productEquiv.toLinearMap
  have hproduct (A : Matrix (V i) (V i) F) (B : Matrix (W i) (W i) F) :
      legAction (kronecker T S) i (productMatrix i A B) ∈ Q := by
    rw [legAction_kronecker]
    rw [← productEquiv_tmul]
    exact Submodule.mem_map_of_mem
      (Lemmata.Centroid.Linear.tmul_mem_tensorSubspace ⟨A, rfl⟩ ⟨B, rfl⟩)
  apply le_antisymm
  · rintro U ⟨M, rfl⟩
    change legAction (kronecker T S) i M ∈ Q
    refine Matrix.induction_on' M ?_ ?_ ?_
    · simpa only [map_zero] using Q.zero_mem
    · intro A B hA hB
      simpa only [map_add] using Q.add_mem hA hB
    · intro a b z
      rw [← productMatrix_single i a.1 b.1 a.2 b.2 z]
      exact hproduct _ _
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.map₂_le.mpr
    rintro U ⟨A, rfl⟩ V ⟨B, rfl⟩
    change productEquiv ((legAction T i A) ⊗ₜ[F] (legAction S i B)) ∈
      actionSpace (kronecker T S) i
    rw [productEquiv_tmul, ← legAction_kronecker]
    exact ⟨productMatrix i A B, rfl⟩

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
def reindexEquiv (e : ∀ i, W i ≃ V i) : Tensor F ι V ≃ₗ[F] Tensor F ι W where
  toFun := restrict fun i => e i
  invFun := restrict fun i => (e i).symm
  left_inv T := by ext x; simp [restrict]
  right_inv T := by ext x; simp [restrict]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
@[simp] theorem reindexEquiv_apply (e : ∀ i, W i ≃ V i) (T : Tensor F ι V)
    (x : ∀ i, W i) : reindexEquiv e T x = T (fun i => e i (x i)) := rfl

omit [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
private theorem reindex_update (e : ∀ i, W i ≃ V i) (x : ∀ i, W i) (i : ι) (a : W i) :
    (fun j => e j (Function.update x i a j)) =
      Function.update (fun j => e j (x j)) i (e i a) := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] in
theorem contraction_reindex (e : ∀ i, W i ≃ V i) (T : Tensor F ι V) (i : ι)
    (u : V i → F) :
    contraction (restrict (fun i => e i) T) i (fun a => u (e i a)) =
      reindexEquiv e (contraction T i u) := by
  ext x
  change (∑ a, u (e i a) * T (fun j => e j (Function.update x i a j))) =
    ∑ a, u a * T (Function.update (fun j => e j (x j)) i a)
  simpa only [reindex_update]
    using Equiv.sum_comp (e i) (fun a => u a * T (Function.update (fun j => e j (x j)) i a))

omit [Fintype ι] in
theorem concise_reindex {T : Tensor F ι V} (hT : Concise T) (e : ∀ i, W i ≃ V i) :
    Concise (restrict (fun i => e i) T) := by
  intro i u v huv
  have hu : (fun a => (u ∘ (e i).symm) (e i a)) = u := by ext; simp
  have hv : (fun a => (v ∘ (e i).symm) (e i a)) = v := by ext; simp
  have h : u ∘ (e i).symm = v ∘ (e i).symm := by
    apply hT i
    apply (reindexEquiv e).injective
    rw [← contraction_reindex, ← contraction_reindex, hu, hv]
    exact huv
  funext a
  simpa using congrFun h (e i a)

omit [Fintype ι] in
theorem concise_reindex_iff (e : ∀ i, W i ≃ V i) (T : Tensor F ι V) :
    Concise (restrict (fun i => e i) T) ↔ Concise T := by
  refine ⟨fun h => ?_, fun h => concise_reindex h e⟩
  have h' := concise_reindex h (fun i => (e i).symm)
  have heq : restrict (fun i => (e i).symm) (restrict (fun i => e i) T) = T := by
    ext x
    simp [restrict]
  rwa [heq] at h'

omit [Fintype ι] in
theorem legAction_reindex (e : ∀ i, W i ≃ V i) (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) :
    legAction (restrict (fun i => e i) T) i (fun a b => A (e i a) (e i b)) =
      reindexEquiv e (legAction T i A) := by
  ext x
  change (∑ a, A (e i (x i)) (e i a) * T (fun j => e j (Function.update x i a j))) =
    ∑ a, A (e i (x i)) a * T (Function.update (fun j => e j (x j)) i a)
  simpa only [reindex_update]
    using Equiv.sum_comp (e i)
      (fun a => A (e i (x i)) a * T (Function.update (fun j => e j (x j)) i a))

omit [Fintype ι] in
theorem actionSpace_reindex (e : ∀ i, W i ≃ V i) (T : Tensor F ι V) (i : ι) :
    actionSpace (restrict (fun i => e i) T) i =
      (actionSpace T i).map (reindexEquiv e).toLinearMap := by
  apply le_antisymm
  · rintro U ⟨B, rfl⟩
    let A : Matrix (V i) (V i) F := fun a b => B ((e i).symm a) ((e i).symm b)
    refine ⟨legAction T i A, ⟨A, rfl⟩, ?_⟩
    change reindexEquiv e (legAction T i A) = legAction _ i B
    rw [← legAction_reindex]
    congr 1
    ext a b
    simp [A]
  · rintro U ⟨_, ⟨A, rfl⟩, rfl⟩
    change reindexEquiv e (legAction T i A) ∈ actionSpace _ i
    rw [← legAction_reindex]
    exact ⟨fun a b => A (e i a) (e i b), rfl⟩

omit [Fintype ι] [∀ i, Fintype (V i)] in
theorem power_add_reindex (T : Tensor F ι V) (m n : ℕ) :
    restrict (fun i => (Fin.appendEquiv m n :
      ((Fin m → V i) × (Fin n → V i)) ≃ (Fin (m + n) → V i)))
      (power T (m + n)) = kronecker (power T m) (power T n) := by
  ext x
  simp only [restrict, power, Fin.appendEquiv, Equiv.coe_fn_mk, kronecker,
    Lemmata.TensorRank.Tensor.reindex,
    Lemmata.TensorRank.Tensor.power,
    Lemmata.TensorRank.Tensor.product]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

omit [Fintype ι] [∀ i, Fintype (V i)] in
theorem power_one_reindex (T : Tensor F ι V) :
    power T 1 = restrict (fun i => Equiv.funUnique (Fin 1) (V i)) T := by
  ext x
  simp [power, restrict, Equiv.funUnique, Equiv.piUnique]

end Lemmata.Centroid.Tensor
