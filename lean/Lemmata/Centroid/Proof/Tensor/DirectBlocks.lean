module

public import Lemmata.Centroid.Proof.Tensor.Maps

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor.Blocks

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]
variable {W : κ → ι → Type*} [∀ m i, Fintype (W m i)]

abbrev Index (W : κ → ι → Type*) (i : ι) := Σ m, W m i

def point (m : κ) (x : ∀ i, W m i) : ∀ i, Index W i := fun i => ⟨m, x i⟩

def component (T : Tensor F ι (Index W)) (m : κ) : Tensor F ι (W m) :=
  fun x => T (point m x)

def IsDiagonal (T : Tensor F ι (Index W)) : Prop :=
  ∀ (x : ∀ i, Index W i) (i j : ι), (x i).1 ≠ (x j).1 → T x = 0

omit [Fintype ι] [Fintype κ] [∀ m i, Fintype (W m i)] in
theorem point_update (m : κ) (x : ∀ i, W m i) (i : ι) (a : W m i) :
    point m (Function.update x i a) = Function.update (point m x) i ⟨m, a⟩ := by
  funext j
  by_cases h : j = i
  · subst j; simp [point]
  · simp only [point, Function.update_of_ne h]

def localPoint (m : κ) (x : ∀ i, Index W i) (h : ∀ i, (x i).1 = m) : ∀ i, W m i :=
  fun i => (h i) ▸ (x i).2

omit [Fintype ι] [Fintype κ] [∀ m i, Fintype (W m i)] in
theorem point_localPoint (m : κ) (x : ∀ i, Index W i) (h : ∀ i, (x i).1 = m) :
    point m (localPoint m x h) = x := by
  funext i
  have hi := h i
  change (⟨m, hi ▸ (x i).2⟩ : Index W i) = x i
  generalize hp : x i = p at hi ⊢
  cases p with
  | mk n a => cases hi; rfl

def extendMatrix (m : κ) (i : ι) (A : Matrix (W m i) (W m i) F) :
    Matrix (Index W i) (Index W i) F :=
  fun p q => if hp : p.1 = m then
    if hq : q.1 = m then A (hp ▸ p.2) (hq ▸ q.2) else 0 else 0

omit [Fintype ι] [Fintype κ] [∀ m i, Fintype (W m i)] in
@[simp] theorem extendMatrix_same (m : κ) (i : ι) (A : Matrix (W m i) (W m i) F)
    (a b : W m i) : extendMatrix m i A ⟨m, a⟩ ⟨m, b⟩ = A a b := by
  simp [extendMatrix]

omit [Fintype ι] in
theorem legAction_extendMatrix_point (T : Tensor F ι (Index W)) (m : κ) (i : ι)
    (A : Matrix (W m i) (W m i) F) (x : ∀ i, W m i) :
    legAction T i (extendMatrix m i A) (point m x) =
      legAction (component T m) i A x := by
  simp only [legAction_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · apply Finset.sum_congr rfl
    intro a _
    change extendMatrix m i A ⟨m, x i⟩ ⟨m, a⟩ *
      T (Function.update (point m x) i ⟨m, a⟩) =
      A (x i) a * T (point m (Function.update x i a))
    rw [extendMatrix_same]
    congr 1
    exact congrArg T (point_update m x i a).symm
  · intro n _ hnm
    apply Finset.sum_eq_zero
    intro a _
    simp only [extendMatrix, point, hnm, dite_false, dite_true, zero_mul]
  · intro hm
    exact (hm (Finset.mem_univ m)).elim

omit [Fintype ι] in
theorem legAction_extendMatrix_zero {T : Tensor F ι (Index W)} (hT : IsDiagonal T)
    (m : κ) (i : ι) (A : Matrix (W m i) (W m i) F) (x : ∀ i, Index W i)
    (hx : ¬ ∀ j, (x j).1 = m) : legAction T i (extendMatrix m i A) x = 0 := by
  simp only [legAction_apply, Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro a _
  by_cases hi : (x i).1 = m
  · by_cases hn : n = m
    · subst n
      obtain ⟨j, hj⟩ := not_forall.mp hx
      have hji : j ≠ i := by intro h; subst j; exact hj hi
      have hzero : T (Function.update x i ⟨m, a⟩) = 0 := by
        apply hT _ i j
        simpa only [Function.update_self, Function.update_of_ne hji] using Ne.symm hj
      rw [hzero, mul_zero]
    · simp only [extendMatrix, hi, hn, dite_false, dite_true, zero_mul]
  · simp only [extendMatrix, hi, dite_false, zero_mul]

theorem legAction_extendMatrix {T : Tensor F ι (Index W)} (hT : IsDiagonal T)
    (m : κ) (i : ι) (A : Matrix (W m i) (W m i) F) (x : ∀ i, Index W i) :
    legAction T i (extendMatrix m i A) x =
      if h : ∀ j, (x j).1 = m then
        legAction (component T m) i A (localPoint m x h) else 0 := by
  by_cases h : ∀ j, (x j).1 = m
  · rw [dite_eq_left h]
    calc
      _ = legAction T i (extendMatrix m i A) (point m (localPoint m x h)) := by
        rw [point_localPoint]
      _ = _ := legAction_extendMatrix_point T m i A _
  · rw [dite_eq_right h]
    exact legAction_extendMatrix_zero hT m i A x h

theorem Concise.component {T : Tensor F ι (Index W)} (hT : Tensor.Concise T)
    (hdiag : IsDiagonal T) (m : κ) : Tensor.Concise (component T m) := by
  apply (concise_iff_legAction_injective _).2
  intro i A B h
  have hglobal : legAction T i (extendMatrix m i A) = legAction T i (extendMatrix m i B) := by
    funext x
    rw [legAction_extendMatrix hdiag, legAction_extendMatrix hdiag]
    split_ifs <;> first | exact congrFun h _ | rfl
  have hmatrix := legAction_injective hT i hglobal
  funext a b
  have hab := congrFun (congrFun hmatrix ⟨m, a⟩) ⟨m, b⟩
  simpa only [extendMatrix_same] using hab

def extendFamily (m : κ) (A : ∀ i, Matrix (W m i) (W m i) F) :
    ∀ i, Matrix (Index W i) (Index W i) F := fun i => extendMatrix m i (A i)

theorem extendFamily_mem_centroid {T : Tensor F ι (Index W)} (hT : IsDiagonal T)
    {m : κ} {A : ∀ i, Matrix (W m i) (W m i) F}
    (hA : A ∈ centroid (component T m)) : extendFamily m A ∈ centroid T := by
  intro i j
  funext x
  change legAction T i (extendMatrix m i (A i)) x =
    legAction T j (extendMatrix m j (A j)) x
  rw [legAction_extendMatrix hT, legAction_extendMatrix hT]
  split_ifs <;> first | exact congrFun (hA i j) _ | rfl

def restrictMatrix (m : κ) (i : ι) (A : Matrix (Index W i) (Index W i) F) :
    Matrix (W m i) (W m i) F := fun a b => A ⟨m, a⟩ ⟨m, b⟩

omit [Fintype ι] in
theorem legAction_point {T : Tensor F ι (Index W)} [Nontrivial ι]
    (hT : IsDiagonal T) (m : κ) (i : ι)
    (A : Matrix (Index W i) (Index W i) F) (x : ∀ i, W m i) :
    legAction T i A (point m x) = legAction (component T m) i (restrictMatrix m i A) x := by
  simp only [legAction_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single m]
  · apply Finset.sum_congr rfl
    intro a _
    change A ⟨m, x i⟩ ⟨m, a⟩ * T (Function.update (point m x) i ⟨m, a⟩) =
      A ⟨m, x i⟩ ⟨m, a⟩ * T (point m (Function.update x i a))
    rw [point_update]
  · intro n _ hnm
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨j, hji⟩ := exists_ne i
    have hzero : T (Function.update (point m x) i ⟨n, a⟩) = 0 := by
      apply hT _ i j
      simpa only [Function.update_self, Function.update_of_ne hji, point] using hnm
    rw [hzero, mul_zero]
  · intro hm
    exact (hm (Finset.mem_univ m)).elim

def restrictCentroid {T : Tensor F ι (Index W)} [Nontrivial ι] (hT : IsDiagonal T)
    (m : κ) : centroid T →ₗ[F] centroid (component T m) where
  toFun A := ⟨fun i => restrictMatrix m i (A.val i), by
    intro i j
    funext x
    rw [← legAction_point hT, ← legAction_point hT]
    exact congrFun (A.property i j) (point m x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendCentroid {T : Tensor F ι (Index W)} (hT : IsDiagonal T)
    (m : κ) : centroid (component T m) →ₗ[F] centroid T where
  toFun A := ⟨extendFamily m A.val, extendFamily_mem_centroid hT A.property⟩
  map_add' A B := by
    apply Subtype.ext
    funext i p q
    change extendMatrix m i (A.val i + B.val i) p q =
      extendMatrix m i (A.val i) p q + extendMatrix m i (B.val i) p q
    simp only [extendMatrix]
    split_ifs <;> simp
  map_smul' c A := by
    apply Subtype.ext
    funext i p q
    change extendMatrix m i (c • A.val i) p q = c * extendMatrix m i (A.val i) p q
    simp only [extendMatrix]
    split_ifs <;> simp

omit [Fintype ι] in
theorem extendMatrix_one_mul (m : κ) (i : ι) (A : Matrix (Index W i) (Index W i) F)
    (p q : Index W i) :
    (extendMatrix m i 1 * A : Matrix (Index W i) (Index W i) F) p q =
      if p.1 = m then A p q else 0 := by
  rcases p with ⟨n, p⟩
  by_cases hn : n = m
  · subst n
    simp only [Matrix.mul_apply, Fintype.sum_sigma, ite_true]
    rw [Finset.sum_eq_single m]
    · simp [extendMatrix, Matrix.one_apply]
    · intro n _ hnm
      simp [extendMatrix, hnm]
    · intro hm
      exact (hm (Finset.mem_univ m)).elim
  · simp [Matrix.mul_apply, extendMatrix, hn]

omit [Fintype ι] in
theorem mul_extendMatrix_one (m : κ) (i : ι) (A : Matrix (Index W i) (Index W i) F)
    (p q : Index W i) :
    (A * extendMatrix m i 1 : Matrix (Index W i) (Index W i) F) p q =
      if q.1 = m then A p q else 0 := by
  rcases q with ⟨n, q⟩
  by_cases hn : n = m
  · subst n
    simp only [Matrix.mul_apply, Fintype.sum_sigma, ite_true]
    rw [Finset.sum_eq_single m]
    · simp [extendMatrix, Matrix.one_apply]
    · intro n _ hnm
      simp [extendMatrix, hnm]
    · intro hm
      exact (hm (Finset.mem_univ m)).elim
  · simp [Matrix.mul_apply, extendMatrix, hn]

theorem blockProjector_mem_centroid {T : Tensor F ι (Index W)} (hT : IsDiagonal T)
    (m : κ) : extendFamily m (fun _ => 1) ∈ centroid T :=
  extendFamily_mem_centroid hT (by intro i j; simp)

end Lemmata.Centroid.Tensor.Blocks

namespace Lemmata.Centroid.Tensor.Blocks

variable {F κ : Type*} [Field F] [Fintype κ]
variable {W : κ → Fin 3 → Type*} [∀ m i, Fintype (W m i)]

theorem centroid_offBlock {T : Tensor F (Fin 3) (Index W)} (hT : Tensor.Concise T)
    (hdiag : IsDiagonal T) (A : centroid T) (i : Fin 3) (p q : Index W i)
    (hpq : p.1 ≠ q.1) : A.val i p q = 0 := by
  have h := centroid_mul_comm hT A.property (blockProjector_mem_centroid hdiag p.1)
  have hpq' := congrFun (congrFun (congrFun h i) p) q
  change (A.val i * extendMatrix p.1 i 1 : Matrix (Index W i) (Index W i) F) p q =
    (extendMatrix p.1 i 1 * A.val i : Matrix (Index W i) (Index W i) F) p q at hpq'
  rw [mul_extendMatrix_one, extendMatrix_one_mul] at hpq'
  simpa only [Ne.symm hpq, ite_false, ite_true] using hpq'.symm

def centroidComponents {T : Tensor F (Fin 3) (Index W)} (hdiag : IsDiagonal T) :
    centroid T →ₗ[F] ∀ m, centroid (component T m) :=
  LinearMap.pi fun m => restrictCentroid hdiag m

theorem centroidComponents_injective {T : Tensor F (Fin 3) (Index W)}
    (hT : Tensor.Concise T) (hdiag : IsDiagonal T) :
    Function.Injective (centroidComponents hdiag) := by
  intro A B h
  apply Subtype.ext
  funext i p q
  by_cases hpq : p.1 = q.1
  · rcases p with ⟨m, p⟩
    rcases q with ⟨n, q⟩
    change m = n at hpq
    subst n
    exact congrFun (congrFun (congrFun (congrArg Subtype.val (congrFun h m)) i) p) q
  · rw [centroid_offBlock hT hdiag A i p q hpq, centroid_offBlock hT hdiag B i p q hpq]

theorem centroidComponents_surjective {T : Tensor F (Fin 3) (Index W)}
    (hdiag : IsDiagonal T) : Function.Surjective (centroidComponents hdiag) := by
  intro A
  let B : centroid T := ∑ m, extendCentroid hdiag m (A m)
  refine ⟨B, ?_⟩
  funext m
  apply Subtype.ext
  funext i p q
  change B.val i ⟨m, p⟩ ⟨m, q⟩ = (A m).val i p q
  simp only [B, Submodule.coe_sum, Finset.sum_apply, Matrix.sum_apply, extendCentroid]
  change (∑ n, extendMatrix n i ((A n).val i) ⟨m, p⟩ ⟨m, q⟩) = (A m).val i p q
  rw [Finset.sum_eq_single m]
  · exact extendMatrix_same m i ((A m).val i) p q
  · intro n _ hnm
    simp [extendMatrix, Ne.symm hnm]
  · intro hm
    exact (hm (Finset.mem_univ m)).elim

def centroidEquiv {T : Tensor F (Fin 3) (Index W)}
    (hT : Tensor.Concise T) (hdiag : IsDiagonal T) :
    centroid T ≃ₗ[F] ∀ m, centroid (component T m) :=
  LinearEquiv.ofBijective (centroidComponents hdiag)
    ⟨centroidComponents_injective hT hdiag, centroidComponents_surjective hdiag⟩

theorem finrank_centroid {T : Tensor F (Fin 3) (Index W)}
    (hT : Tensor.Concise T) (hdiag : IsDiagonal T) :
    Module.finrank F (centroid T) = ∑ m, Module.finrank F (centroid (component T m)) := by
  rw [(centroidEquiv hT hdiag).finrank_eq, Module.finrank_pi_fintype]

end Lemmata.Centroid.Tensor.Blocks
