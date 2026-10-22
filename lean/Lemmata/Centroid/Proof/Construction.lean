module

public import Lemmata.Centroid.Proof.BigCentroid
public import Lemmata.Centroid.Proof.Centroid
public import Mathlib.Algebra.Module.Projective

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid.Realization

noncomputable section

variable {F ι : Type*} [Field F] [Fintype ι]
variable {U L : ι → Type*} [∀ i, Fintype (U i)]

abbrev Coordinates (U L : ι → Type*) (i : ι) := U i ⊕ L i

abbrev Opposite (U : ι → Type*) (i : ι) := ∀ j : {j // j ≠ i}, U j.val

abbrev PairFamily (F : Type*) (U L : ι → Type*) :=
  ∀ i, L i → Opposite U i → F

def coreEntry (i : ι) (x : Coordinates U L i) (a : U i) : F :=
  match x with
  | Sum.inl b => if a = b then 1 else 0
  | Sum.inr _ => 0

def coreEmbedding : Tensor F ι U →ₗ[F] Tensor F ι (Coordinates U L) where
  toFun := Tensor.localMap coreEntry
  map_add' := Tensor.localMap_add coreEntry
  map_smul' := Tensor.localMap_smul coreEntry

theorem coreEmbedding_core (T : Tensor F ι U) (a : ∀ i, U i) :
    coreEmbedding (L := L) T (fun i => Sum.inl (a i)) = T a := by
  change (∑ b, (∏ i, coreEntry i (Sum.inl (a i)) (b i)) * T b) = T a
  rw [Finset.sum_eq_single a]
  · simp [coreEntry]
  · intro b hb hba
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hba
    have hz : (∏ i, coreEntry (F := F) (L := L) i (Sum.inl (a i)) (b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coreEntry, hi])
    rw [hz, zero_mul]
  · simp

theorem coreEmbedding_dual (T : Tensor F ι U) (x : ∀ i, Coordinates U L i)
    (i : ι) (l : L i) (hx : x i = Sum.inr l) : coreEmbedding T x = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have hz : (∏ j, coreEntry (F := F) j (x j) (a j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coreEntry, hx])
  exact mul_eq_zero_of_left hz _

theorem coreEmbedding_injective : Function.Injective (coreEmbedding (F := F) (U := U) (L := L)) := by
  intro T S h
  funext a
  simpa only [coreEmbedding_core] using congrFun h (fun i => Sum.inl (a i))

def pairEmbedding (i : ι) (P : Opposite U i → F) :
    Tensor F ι (Coordinates U L) :=
  fun x => ∑ a : Opposite U i, P a *
    ∏ j : {j // j ≠ i}, coreEntry j.val (x j.val) (a j)

theorem pairEmbedding_update (i : ι) (P : Opposite U i → F)
    (x : ∀ j, Coordinates U L j) (v : Coordinates U L i) :
    pairEmbedding i P (Function.update x i v) = pairEmbedding i P x := by
  unfold pairEmbedding
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne j.property]

theorem pairEmbedding_dual (i j : ι) (hji : j ≠ i) (P : Opposite U i → F)
    (x : ∀ k, Coordinates U L k) (l : L j) (hx : x j = Sum.inr l) :
    pairEmbedding i P x = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have hz : (∏ k : {k // k ≠ i}, coreEntry (F := F) k.val (x k.val) (a k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {k // k ≠ i}))
      (by simp [coreEntry, hx])
  rw [hz, mul_zero]

theorem pairEmbedding_core (i : ι) (P : Opposite U i → F) (a : ∀ j, U j) :
    pairEmbedding (L := L) i P (fun j => Sum.inl (a j)) = P (fun j => a j.val) := by
  unfold pairEmbedding
  rw [Finset.sum_eq_single (fun j : {j // j ≠ i} => a j.val)]
  · simp [coreEntry]
  · intro b hb hba
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hba
    have hz : (∏ j : {j // j ≠ i}, coreEntry (F := F) (L := L) j.val
        (Sum.inl (a j.val)) (b j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [coreEntry, hj])
    rw [hz, mul_zero]
  · simp

def sector (P : PairFamily F U L) (i : ι) : Tensor F ι (Coordinates U L) :=
  fun x => match x i with
    | Sum.inl _ => 0
    | Sum.inr l => pairEmbedding i (P i l) x

def tensor (P : PairFamily F U L) (τ : Tensor F ι U) :
    Tensor F ι (Coordinates U L) := (∑ i, sector P i) + coreEmbedding τ

theorem tensor_dual_slice (P : PairFamily F U L) (τ : Tensor F ι U)
    (i : ι) (l : L i) (x : ∀ j, Coordinates U L j) :
    tensor P τ (Function.update x i (Sum.inr l)) = pairEmbedding i (P i l) x := by
  simp only [tensor, Pi.add_apply, Finset.sum_apply]
  rw [coreEmbedding_dual τ _ i l (Function.update_self _ _ _), add_zero]
  rw [Finset.sum_eq_single i]
  · simp [sector, pairEmbedding_update]
  · intro j hj hji
    unfold sector
    split
    · rfl
    · exact pairEmbedding_dual j i (Ne.symm hji) _ _ l (Function.update_self _ _ _)
  · simp

variable [∀ i, Fintype (L i)]

def reconstruction (P : PairFamily F U L) (i : ι) :
    (U i → L i → F) →ₗ[F] Tensor F ι U where
  toFun A x := ∑ l, A (x i) l * P i l (fun j => x j.val)
  map_add' A B := by ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by ext x; simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

def compatibleSpace (P : PairFamily F U L) : Submodule F (Tensor F ι U) :=
  ⨅ i, (reconstruction P i).range

def radicalMatrix (A : ∀ i, U i → L i → F) (i : ι) :
    Matrix (Coordinates U L i) (Coordinates U L i) F :=
  fun r c => match r, c with
    | Sum.inl a, Sum.inr l => A i a l
    | _, _ => 0

theorem radicalAction_core (P : PairFamily F U L) (τ : Tensor F ι U)
    (A : ∀ i, U i → L i → F) (i : ι) (a : ∀ j, U j) :
    Tensor.legAction (tensor P τ) i (radicalMatrix A i) (fun j => Sum.inl (a j)) =
      reconstruction P i (A i) a := by
  simp [Tensor.legAction_apply, Fintype.sum_sum_type, radicalMatrix,
    tensor_dual_slice, pairEmbedding_core, reconstruction]

theorem radicalAction_dual (P : PairFamily F U L) (τ : Tensor F ι U)
    (A : ∀ i, U i → L i → F) (i j : ι)
    (x : ∀ k, Coordinates U L k) (l : L j) (hx : x j = Sum.inr l) :
    Tensor.legAction (tensor P τ) i (radicalMatrix A i) x = 0 := by
  by_cases hji : j = i
  · subst j
    simp [Tensor.legAction_apply, radicalMatrix, hx]
  · have hz (l' : L i) : pairEmbedding i (P i l') x = 0 :=
      pairEmbedding_dual i j hji _ x l hx
    cases hxi : x i <;>
      simp [Tensor.legAction_apply, Fintype.sum_sum_type, radicalMatrix,
        hxi, tensor_dual_slice, hz]

theorem radicalAction (P : PairFamily F U L) (τ Z : Tensor F ι U)
    (A : ∀ i, U i → L i → F) (hA : ∀ i, reconstruction P i (A i) = Z) (i : ι) :
    Tensor.legAction (tensor P τ) i (radicalMatrix A i) = coreEmbedding Z := by
  funext x
  by_cases hd : ∃ j l, x j = Sum.inr l
  · obtain ⟨j, l, hx⟩ := hd
    rw [radicalAction_dual P τ A i j x l hx, coreEmbedding_dual Z x j l hx]
  · have hcore (j : ι) : ∃ a : U j, x j = Sum.inl a := by
      cases hx : x j with
      | inl a => exact ⟨a, rfl⟩
      | inr l => exact False.elim (hd ⟨j, l, hx⟩)
    choose a ha using hcore
    have hx : x = fun j => Sum.inl (a j) := funext ha
    rw [hx, radicalAction_core, coreEmbedding_core]
    exact congrFun (hA i) a

def reconstructionSection (P : PairFamily F U L) (i : ι) :
    (reconstruction P i).range →ₗ[F] (U i → L i → F) :=
  Classical.choose ((reconstruction P i).rangeRestrict.exists_rightInverse_of_surjective
    (reconstruction P i).range_rangeRestrict)

omit [Fintype ι] in
theorem reconstructionSection_rightInverse (P : PairFamily F U L) (i : ι) :
    (reconstruction P i).rangeRestrict.comp (reconstructionSection P i) = LinearMap.id :=
  Classical.choose_spec ((reconstruction P i).rangeRestrict.exists_rightInverse_of_surjective
    (reconstruction P i).range_rangeRestrict)

def compatibleInclusion (P : PairFamily F U L) (i : ι) :
    compatibleSpace P →ₗ[F] (reconstruction P i).range where
  toFun Z := ⟨Z.val, (Submodule.mem_iInf (fun j => (reconstruction P j).range)).mp Z.property i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficients (P : PairFamily F U L) (i : ι) :
    compatibleSpace P →ₗ[F] (U i → L i → F) :=
  (reconstructionSection P i).comp (compatibleInclusion P i)

omit [Fintype ι] in
theorem reconstruction_coefficients (P : PairFamily F U L) (Z : compatibleSpace P) (i : ι) :
    reconstruction P i (coefficients P i Z) = Z.val := by
  have h := congrArg (fun f : (reconstruction P i).range →ₗ[F] (reconstruction P i).range =>
    f (compatibleInclusion P i Z)) (reconstructionSection_rightInverse P i)
  exact congrArg Subtype.val h

def radical (P : PairFamily F U L) (τ : Tensor F ι U) :
    compatibleSpace P →ₗ[F] Tensor.centroid (tensor P τ) where
  toFun Z := ⟨radicalMatrix (fun i => coefficients P i Z), fun i j =>
    (radicalAction P τ Z.val _ (reconstruction_coefficients P Z) i).trans
      (radicalAction P τ Z.val _ (reconstruction_coefficients P Z) j).symm⟩
  map_add' Z W := by
    apply Subtype.ext
    funext i r c
    cases r <;> cases c <;> simp [radicalMatrix, map_add]
  map_smul' c Z := by
    apply Subtype.ext
    funext i r s
    cases r <;> cases s <;> simp [radicalMatrix, map_smul]

theorem radical_injective [Nonempty ι] (P : PairFamily F U L) (τ : Tensor F ι U) :
    Function.Injective (radical P τ) := by
  intro Z W h
  let i : ι := Classical.choice inferInstance
  have hh := congrArg (fun A : Tensor.centroid (tensor P τ) =>
    Tensor.legAction (tensor P τ) i (A.val i)) h
  change Tensor.legAction (tensor P τ) i (radicalMatrix (fun i => coefficients P i Z) i) =
    Tensor.legAction (tensor P τ) i (radicalMatrix (fun i => coefficients P i W) i) at hh
  rw [radicalAction P τ Z.val _ (reconstruction_coefficients P Z) i,
    radicalAction P τ W.val _ (reconstruction_coefficients P W) i] at hh
  exact Subtype.ext (coreEmbedding_injective hh)

def identity (P : PairFamily F U L) (τ : Tensor F ι U) :
    Tensor.centroid (tensor P τ) :=
  ⟨fun _ => 1, fun i j => by
    ext x
    simp [Tensor.legAction_apply, Matrix.one_apply]⟩

def augmented (P : PairFamily F U L) (τ : Tensor F ι U) :
    (F × compatibleSpace P) →ₗ[F] Tensor.centroid (tensor P τ) where
  toFun x := x.1 • identity P τ + radical P τ x.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]; abel
  map_smul' c x := by simp [smul_add, mul_smul]

theorem augmented_injective [Nonempty ι] [∀ i, Nonempty (U i)]
    (P : PairFamily F U L) (τ : Tensor F ι U) : Function.Injective (augmented P τ) := by
  rintro ⟨c, Z⟩ ⟨d, W⟩ h
  let i : ι := Classical.choice inferInstance
  let a : U i := Classical.choice inferInstance
  have hcd := congrArg (fun A : Tensor.centroid (tensor P τ) =>
    A.val i (Sum.inl a) (Sum.inl a)) h
  have hc : c = d := by
    simpa [augmented, identity, radical, radicalMatrix] using hcd
  subst d
  have hZW : Z = W := radical_injective P τ (add_left_cancel
    (show c • identity P τ + radical P τ Z = c • identity P τ + radical P τ W from h))
  exact Prod.ext rfl hZW

theorem centroid_lower_bound [Nonempty ι] [∀ i, Nonempty (U i)]
    (P : PairFamily F U L) (τ : Tensor F ι U) :
    1 + Module.finrank F (compatibleSpace P) ≤
      Module.finrank F (Tensor.centroid (tensor P τ)) := by
  simpa only [Module.finrank_prod, Module.finrank_self] using
    LinearMap.finrank_le_finrank_of_injective (augmented_injective P τ)

omit [Fintype ι] in
theorem radicalMatrix_mul (A B : ∀ i, U i → L i → F) (i : ι) :
    radicalMatrix A i * radicalMatrix B i = 0 := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.zero_apply, Fintype.sum_sum_type]
  cases r <;> cases c <;> simp [radicalMatrix]

def fullPairs : PairFamily F U (Opposite U) :=
  fun _ l p => if p = l then 1 else 0

theorem pairEmbedding_full (i : ι) (p : Opposite U i)
    (x : ∀ j, BigCentroid.Coordinates U j) :
    pairEmbedding i (fullPairs (F := F) i p) x = BigCentroid.pairCoefficient i p x := by
  simp only [pairEmbedding, fullPairs, ite_mul, one_mul, zero_mul,
    Fintype.sum_ite_eq']
  apply Finset.prod_congr rfl
  intro j hj
  cases x j.val <;> simp [coreEntry, eq_comm]

theorem tensor_full :
    tensor (fullPairs (F := F) (U := U)) 0 = BigCentroid.tensor (F := F) (U := U) := by
  ext x
  simp only [tensor, map_zero, add_zero, BigCentroid.tensor, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold sector BigCentroid.sector
  cases x i
  · rfl
  · exact pairEmbedding_full i _ x

def assemble (i : ι) (a : U i) (p : Opposite U i) : ∀ j, U j :=
  fun j => if h : j = i then h.symm ▸ a else p ⟨j, h⟩

omit [Fintype ι] [∀ i, Fintype (U i)] in
@[simp] theorem assemble_restrict (x : ∀ j, U j) (i : ι) :
    assemble i (x i) (fun j => x j.val) = x := by
  funext j
  by_cases h : j = i
  · subst j; simp [assemble]
  · simp [assemble, h]

theorem reconstruction_full (Z : Tensor F ι U) (i : ι) :
    reconstruction fullPairs i (fun a p => Z (assemble i a p)) = Z := by
  ext x
  simp [reconstruction, fullPairs, mul_ite, assemble_restrict]

theorem compatibleSpace_full : compatibleSpace (fullPairs (F := F) (U := U)) = ⊤ := by
  apply le_antisymm le_top
  intro Z hZ
  apply (Submodule.mem_iInf _).mpr
  intro i
  exact ⟨_, reconstruction_full Z i⟩

theorem full_centroid_lower_bound [Nonempty ι] [∀ i, Nonempty (U i)] :
    1 + ∏ i, Fintype.card (U i) ≤
      Module.finrank F (Tensor.centroid (BigCentroid.tensor (F := F) (U := U))) := by
  have h := centroid_lower_bound (fullPairs (F := F) (U := U)) 0
  rw [tensor_full, compatibleSpace_full, finrank_top] at h
  simpa only [Tensor, Module.finrank_fintype_fun_eq_card, Fintype.card_pi] using h

end

end Lemmata.Centroid.Realization

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] {V : ι → Type*} [∀ i, Fintype (V i)]

theorem concise_of_identity_minors (T : Tensor F ι V)
    (column : ∀ i, V i → ∀ j, V j)
    (hcolumn : ∀ i, flatteningMinor T i id (column i) = 1) : Concise T := by
  intro i f g h
  funext a
  have hc (b : V i) : T (Function.update (column i a) i b) = if b = a then 1 else 0 := by
    exact congrFun (congrFun (hcolumn i) b) a
  have hv := congrFun h (column i a)
  simpa [contraction_apply, hc, mul_ite] using hv

end Lemmata.Centroid.Tensor

namespace Lemmata.Centroid.BigCentroid

variable {F ι : Type*} [Field F] [Fintype ι] [Nontrivial ι]
variable {U : ι → Type*} [∀ i, Fintype (U i)] [∀ i, Nonempty (U i)]

theorem concise : Tensor.Concise (tensor (F := F) (U := U)) := by
  classical
  have hj (i : ι) : ∃ j, i ≠ j := exists_ne i |>.imp (fun _ h => h.symm)
  choose j hj using hj
  let a : ∀ i, U i := fun _ => Classical.choice inferInstance
  apply Tensor.concise_of_identity_minors _ (fun i => minorColumn i (j i) a)
  intro i
  convert flatteningMinor_identity (F := F) i (j i) (hj i) a using 1
  ext r c
  simp [Matrix.one_apply]

end Lemmata.Centroid.BigCentroid
