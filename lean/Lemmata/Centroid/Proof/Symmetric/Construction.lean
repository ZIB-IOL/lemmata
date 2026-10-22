module

public import Lemmata.Centroid.Proof.Symmetric.Graph
public import Lemmata.Centroid.Proof.Construction
public import Lemmata.Centroid.Proof.Construction.DirectSum
public import Lemmata.Centroid.Proof.Construction.Diagonal

@[expose] public section

namespace Lemmata.Centroid.Symmetric.Construction

open scoped BigOperators
open Classical

noncomputable section

variable {F K : Type*} [Field F] [Fintype K]

def pairOrbit (i : Fin 3) (p : Realization.Opposite (fun _ : Fin 3 => K) i) : Sym K 2 :=
  orbit (fun j => p ⟨i.succAbove j, Fin.succAbove_ne i j⟩)

omit [Fintype K] in theorem orbit_eq_cons_pair (i : Fin 3) (x : Fin 3 → K) :
    orbit x = Sym.cons (x i) (pairOrbit i (fun j => x j.val)) := by
  fin_cases i <;> apply Sym.ext
  · rfl
  · change x 0 ::ₘ x 1 ::ₘ x 2 ::ₘ (0 : Multiset K) = x 1 ::ₘ x 0 ::ₘ x 2 ::ₘ 0
    exact Multiset.cons_swap _ _ _
  · change x 0 ::ₘ x 1 ::ₘ x 2 ::ₘ (0 : Multiset K) = x 2 ::ₘ x 0 ::ₘ x 1 ::ₘ 0
    rw [Multiset.cons_swap (x 2) (x 0), Multiset.cons_swap (x 2) (x 1)]

def pairs (Q : Finset (Sym K 2)) :
    Realization.PairFamily F (fun _ : Fin 3 => K) (fun _ => Q) :=
  fun i q p => if pairOrbit i p = q.val then 1 else 0

def tensor (Q : Finset (Sym K 2)) : Cubic F (K ⊕ Q) := Realization.tensor (pairs Q) 0

abbrev FullCoordinates (K : Type*) [Fintype K] := K ⊕ (Finset.univ : Finset (Sym K 2))

theorem tensor_core (Q : Finset (Sym K 2)) (a : Fin 3 → K) :
    tensor (F := F) Q (fun i => Sum.inl (a i)) = 0 := by
  simp [tensor, Realization.tensor, Realization.sector]

theorem tensor_single_dual (Q : Finset (Sym K 2)) (i : Fin 3) (q : Q) (a : Fin 3 → K) :
    tensor (F := F) Q (Function.update (fun j => Sum.inl (a j)) i (Sum.inr q)) =
      if pairOrbit i (fun j => a j.val) = q.val then 1 else 0 := by
  have h := Realization.tensor_dual_slice (pairs (F := F) Q) 0 i q (fun j => Sum.inl (a j))
  rw [Realization.pairEmbedding_core] at h
  change _ = (if pairOrbit i (fun j => a j.val) = q.val then 1 else 0) at h
  convert h using 1
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem tensor_two_dual (Q : Finset (Sym K 2)) (x : Fin 3 → K ⊕ Q)
    (i j : Fin 3) (q r : Q) (hji : j ≠ i) (hi : x i = Sum.inr q) (hj : x j = Sum.inr r) :
    tensor (F := F) Q x = 0 := by
  have hx : Function.update x i (Sum.inr q) = x := Function.update_eq_self_iff.2 hi.symm
  calc
    tensor Q x = Realization.tensor (pairs Q) 0 (Function.update x i (Sum.inr q)) :=
      congrArg (tensor (F := F) Q) hx.symm
    _ = Realization.pairEmbedding i (pairs Q i q) x := by
      convert Realization.tensor_dual_slice (pairs (F := F) Q) 0 i q x using 1
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk]
    _ = 0 := Realization.pairEmbedding_dual i j hji _ x r hj

omit [Fintype K] in theorem pairOrbit_permutation (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (a : Fin 3 → K) :
    pairOrbit (σ.symm i) (fun j => a (σ j.val)) = pairOrbit i (fun j => a j.val) := by
  apply (Sym.cons_inj_right (a i) _ _).1
  calc
    _ = orbit (a ∘ σ) := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        (orbit_eq_cons_pair (σ.symm i) (a ∘ σ)).symm
    _ = orbit a := orbit_permute σ a
    _ = _ := orbit_eq_cons_pair i a

omit [Fintype K] in theorem permute_update {L : Type*} (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (q : L) (a : Fin 3 → K) :
    (fun j => Function.update (fun k => Sum.inl (a k)) i (Sum.inr q) (σ j)) =
      Function.update (fun j => Sum.inl (a (σ j))) (σ.symm i) (Sum.inr q) := by
  funext j
  by_cases hj : j = σ.symm i
  · subst j
    simp
  · have hσ : σ j ≠ i := fun h => hj (σ.injective (by simpa only [Equiv.apply_symm_apply] using h))
    simp only [Function.update_of_ne hσ, Function.update_of_ne hj]

theorem tensor_isSymmetric [Nonempty K] (Q : Finset (Sym K 2)) :
    Cubic.IsSymmetric (tensor (F := F) Q) := by
  intro σ x
  by_cases hd : ∃ i q, x i = Sum.inr q
  · obtain ⟨i, q, hi⟩ := hd
    by_cases hd' : ∃ j r, j ≠ i ∧ x j = Sum.inr r
    · obtain ⟨j, r, hji, hj⟩ := hd'
      have hji' : σ.symm j ≠ σ.symm i := fun he => hji (σ.symm.injective he)
      rw [tensor_two_dual Q x i j q r hji hi hj]
      exact tensor_two_dual Q (fun k => x (σ k)) (σ.symm i) (σ.symm j) q r hji'
        (by simpa only [Equiv.apply_symm_apply] using hi)
        (by simpa only [Equiv.apply_symm_apply] using hj)
    · let a : Fin 3 → K := fun j => match x j with
        | Sum.inl k => k
        | Sum.inr _ => Classical.choice inferInstance
      have hx : x = Function.update (fun j => Sum.inl (a j)) i (Sum.inr q) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, hi]
        · rw [Function.update_of_ne hji]
          cases hj : x j with
          | inl k => simp [a, hj]
          | inr r => exact False.elim (hd' ⟨j, r, hji, hj⟩)
      rw [hx, permute_update, tensor_single_dual, tensor_single_dual, pairOrbit_permutation]
  · have hall (i : Fin 3) : ∃ k, x i = Sum.inl k := by
      cases hi : x i with
      | inl k => exact ⟨k, rfl⟩
      | inr q => exact False.elim (hd ⟨i, q, hi⟩)
    choose a ha using hall
    have hx : x = fun i => Sum.inl (a i) := funext ha
    rw [hx, tensor_core, tensor_core]

theorem tensor_dual_core_core (Q : Finset (Sym K 2)) (q : Q) (a b : K) :
    tensor (F := F) Q ![Sum.inr q, Sum.inl a, Sum.inl b] =
      if quadricMonomial a b = q.val then 1 else 0 := by
  have hx : ![Sum.inr q, Sum.inl a, Sum.inl b] =
      Function.update (fun j => Sum.inl (![a, a, b] j)) 0 (Sum.inr q) := by
    funext j
    fin_cases j <;> simp
  rw [hx, tensor_single_dual]
  rfl

theorem tensor_core_dual_core (Q : Finset (Sym K 2)) (q : Q) (a b : K) :
    tensor (F := F) Q ![Sum.inl a, Sum.inr q, Sum.inl b] =
      if quadricMonomial a b = q.val then 1 else 0 := by
  have hx : ![Sum.inl a, Sum.inr q, Sum.inl b] =
      Function.update (fun j => Sum.inl (![a, a, b] j)) 1 (Sum.inr q) := by
    funext j
    fin_cases j <;> simp
  rw [hx, tensor_single_dual]
  rfl

private theorem contraction_permute {L : Type*} [Fintype L] (σ : Equiv.Perm (Fin 3))
    (T : Cubic F L) (i : Fin 3) (u : L → F) :
    Cubic.permute σ (Tensor.contraction T i u) =
      Tensor.contraction (Cubic.permute σ T) (σ i) u := by
  ext x
  simp only [Cubic.permute_apply, Tensor.contraction_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update, h, σ.injective.ne h]

theorem concise_of_first {L : Type*} [Fintype L] {T : Cubic F L}
    (hs : Cubic.IsSymmetric T) (h0 : Function.Injective (Tensor.contraction T 0)) : Tensor.Concise T := by
  intro i f g hfg
  apply h0
  let σ := Equiv.swap 0 i
  have hinj : Function.Injective (Cubic.permute (F := F) (I := L) σ) := by
    intro R S h
    funext x
    have hx := congrFun h (fun j => x (σ.symm j))
    change R (fun i => x (σ.symm (σ i))) = S (fun i => x (σ.symm (σ i))) at hx
    have heq : (fun i => x (σ.symm (σ i))) = x := by
      funext i
      rw [Equiv.symm_apply_apply]
    rwa [heq] at hx
  apply hinj
  rw [contraction_permute, contraction_permute, Cubic.permute_eq hs]
  simpa only [σ, Equiv.swap_apply_left] using hfg

theorem tensor_core_core_core (Q : Finset (Sym K 2)) (a b c : K) :
    tensor (F := F) Q ![Sum.inl a, Sum.inl b, Sum.inl c] = 0 := by
  convert tensor_core (F := F) Q ![a, b, c] using 1
  congr 1
  funext i
  fin_cases i <;> rfl

theorem tensor_dual_dual_core (Q : Finset (Sym K 2)) (q r : Q) (a : K) :
    tensor (F := F) Q ![Sum.inr q, Sum.inr r, Sum.inl a] = 0 :=
  tensor_two_dual Q _ 0 1 q r (by decide) rfl rfl

theorem contraction_core_pair (Q : Finset (Sym K 2)) (u : K ⊕ Q → F) (a b c : K) :
    Tensor.contraction (tensor Q) 0 u ![Sum.inl a, Sum.inl b, Sum.inl c] =
      ∑ q : Q, u (Sum.inr q) * (if quadricMonomial b c = q.val then 1 else 0) := by
  simp only [Tensor.contraction_apply, Tensor.update_three_zero, Fintype.sum_sum_type,
    tensor_core_core_core, tensor_dual_core_core, mul_zero, Finset.sum_const_zero, zero_add]

theorem contraction_dual_core (Q : Finset (Sym K 2)) (u : K ⊕ Q → F) (a b : K) (q : Q) :
    Tensor.contraction (tensor Q) 0 u ![Sum.inl a, Sum.inr q, Sum.inl b] =
      ∑ z : K, u (Sum.inl z) * (if quadricMonomial z b = q.val then 1 else 0) := by
  simp only [Tensor.contraction_apply, Tensor.update_three_zero, Fintype.sum_sum_type,
    tensor_core_dual_core, tensor_dual_dual_core, mul_zero, Finset.sum_const_zero, add_zero]

theorem concise [Nonempty K] (Q : Finset (Sym K 2))
    (hsupport : ∀ a : K, ∃ b, quadricMonomial a b ∈ Q) : Tensor.Concise (tensor (F := F) Q) := by
  apply concise_of_first (tensor_isSymmetric Q)
  intro f g hfg
  funext x
  cases x with
  | inl a =>
    obtain ⟨b, hb⟩ := hsupport a
    let q : Q := ⟨quadricMonomial a b, hb⟩
    have hpair (z : K) : quadricMonomial z b = q.val ↔ z = a :=
      Sym.cons_inj_left z a (Sym.oneEquiv b)
    have h := congrFun hfg ![Sum.inl a, Sum.inr q, Sum.inl b]
    rw [contraction_dual_core, contraction_dual_core] at h
    simpa only [hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using h
  | inr q =>
    obtain ⟨a, t, ht⟩ := Sym.exists_eq_cons_of_succ q.val
    obtain ⟨b, hb⟩ := Sym.oneEquiv.surjective t
    have hq : q.val = quadricMonomial a b := by rw [ht, ← hb]; rfl
    have hpair (r : Q) : quadricMonomial a b = r.val ↔ r = q := by
      rw [← hq]
      exact ⟨fun h => Subtype.ext h.symm, fun h => congrArg Subtype.val h.symm⟩
    have h := congrFun hfg ![Sum.inl a, Sum.inl a, Sum.inl b]
    rw [contraction_core_pair, contraction_core_pair] at h
    simpa only [hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using h

def prolongation (Q : Finset (Sym K 2)) : Submodule F (Coefficients F K 3) where
  carrier := {c | ∀ i q, q ∉ Q → c (Sym.cons i q) = 0}
  zero_mem' := by simp
  add_mem' := by intro c d hc hd i q hq; simp only [Pi.add_apply, hc i q hq, hd i q hq, add_zero]
  smul_mem' := by intro a c hc i q hq; simp only [Pi.smul_apply, hc i q hq, smul_zero]

def reconstructionCoefficients (Q : Finset (Sym K 2)) (c : Coefficients F K 3)
    (_i : Fin 3) : K → Q → F := fun a q => c (Sym.cons a q.val)

omit [Fintype K] in theorem reconstruction_eq (Q : Finset (Sym K 2)) {c : Coefficients F K 3}
    (hc : c ∈ prolongation Q) (i : Fin 3) :
    Realization.reconstruction (pairs Q) i (reconstructionCoefficients Q c i) = toTensor 3 c := by
  classical
  ext x
  simp only [Realization.reconstruction, pairs, reconstructionCoefficients,
    LinearMap.coe_mk, AddHom.coe_mk, toTensor, mul_ite, mul_one, mul_zero]
  by_cases hq : pairOrbit i (fun j => x j.val) ∈ Q
  · rw [Finset.sum_eq_single ⟨_, hq⟩]
    · rw [← orbit_eq_cons_pair]
      simp
    · intro q hq' hne
      have hval : pairOrbit i (fun j => x j.val) ≠ q.val := by
        intro he
        exact hne (Subtype.ext he.symm)
      simp only [hval, ite_false]
    · simp
  · have hz := hc (x i) _ hq
    rw [← orbit_eq_cons_pair] at hz
    rw [hz]
    apply Finset.sum_eq_zero
    intro q _
    have hval : pairOrbit i (fun j => x j.val) ≠ q.val := by
      intro he
      exact hq (he ▸ q.property)
    simp only [hval, ite_false]

def compatibleInclusion (Q : Finset (Sym K 2)) :
    prolongation (F := F) Q →ₗ[F] Realization.compatibleSpace (pairs (F := F) Q) where
  toFun c := ⟨toTensor 3 c.val, by
    apply (Submodule.mem_iInf _).2
    intro i
    exact ⟨reconstructionCoefficients Q c.val i, reconstruction_eq Q c.property i⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

omit [Fintype K] in theorem compatibleInclusion_injective (Q : Finset (Sym K 2)) :
    Function.Injective (compatibleInclusion (F := F) Q) := by
  intro c d he
  exact Subtype.ext (toTensor_injective 3 (congrArg Subtype.val he))

theorem centroid_lower_bound [Nonempty K] (Q : Finset (Sym K 2)) :
    1 + Module.finrank F (prolongation (F := F) Q) ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) Q)) := by
  have h₁ := LinearMap.finrank_le_finrank_of_injective (compatibleInclusion_injective (F := F) Q)
  have h₂ := Realization.centroid_lower_bound (pairs (F := F) Q) 0
  exact (Nat.add_le_add_left h₁ 1).trans h₂

def familyInclusion (Q : Finset (Sym K 2)) (C : Finset (Sym K 3))
    (hC : ∀ s ∈ C, ∀ i q, s = Sym.cons i q → q ∈ Q) :
    (C → F) →ₗ[F] prolongation (F := F) Q where
  toFun f := ⟨fun s => if h : s ∈ C then f ⟨s, h⟩ else 0, by
    intro i q hq
    have hs : Sym.cons i q ∉ C := fun hs => hq (hC _ hs i q rfl)
    simp only [hs, dite_false]⟩
  map_add' f g := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ C <;> simp [hs]
  map_smul' a f := by
    apply Subtype.ext
    funext s
    by_cases hs : s ∈ C <;> simp [hs]

omit [Fintype K] in
theorem familyInclusion_injective (Q : Finset (Sym K 2)) (C : Finset (Sym K 3))
    (hC : ∀ s ∈ C, ∀ i q, s = Sym.cons i q → q ∈ Q) :
    Function.Injective (familyInclusion (F := F) Q C hC) := by
  intro f g hfg
  funext s
  have h := congrFun (congrArg Subtype.val hfg) s.val
  change (if h : s.val ∈ C then f ⟨s.val, h⟩ else 0) =
    (if h : s.val ∈ C then g ⟨s.val, h⟩ else 0) at h
  simpa only [s.property, dite_true] using h

theorem family_dimension_lower_bound (Q : Finset (Sym K 2)) (C : Finset (Sym K 3))
    (hC : ∀ s ∈ C, ∀ i q, s = Sym.cons i q → q ∈ Q) :
    C.card ≤ Module.finrank F (prolongation (F := F) Q) := by
  have h := LinearMap.finrank_le_finrank_of_injective (familyInclusion_injective (F := F) Q C hC)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

theorem centroid_family_lower_bound [Nonempty K] (Q : Finset (Sym K 2)) (C : Finset (Sym K 3))
    (hC : ∀ s ∈ C, ∀ i q, s = Sym.cons i q → q ∈ Q) :
    1 + C.card ≤ Module.finrank F (Tensor.centroid (tensor (F := F) Q)) :=
  (Nat.add_le_add_left (family_dimension_lower_bound Q C hC) 1).trans (centroid_lower_bound Q)

@[simp] theorem prolongation_univ : prolongation (F := F) (Finset.univ : Finset (Sym K 2)) = ⊤ := by
  ext c
  simp [prolongation]

theorem full_centroid_lower_bound [Nonempty K] :
    1 + (Fintype.card K + 2).choose 3 ≤
      Module.finrank F (Tensor.centroid (tensor (F := F) (Finset.univ : Finset (Sym K 2)))) := by
  have h := centroid_lower_bound (F := F) (Finset.univ : Finset (Sym K 2))
  rw [prolongation_univ, finrank_top, finrank_coefficients] at h
  have hindex : Fintype.card K + 3 - 1 = Fintype.card K + 2 := by omega
  rwa [hindex] at h

theorem full_concise [Nonempty K] :
    Tensor.Concise (tensor (F := F) (Finset.univ : Finset (Sym K 2))) :=
  concise _ (fun a => ⟨a, Finset.mem_univ _⟩)

theorem full_format :
    Fintype.card (FullCoordinates K) = symmetricBase (Fintype.card K) := by
  classical
  simp only [Fintype.card_sum, Fintype.card_coe, Finset.card_univ, Sym.card_sym_eq_choose]
  have hindex : Fintype.card K + 2 - 1 = Fintype.card K + 1 := by omega
  rw [hindex]
  have htwo := two_mul_choose_two_succ (Fintype.card K)
  have hpoly : Fintype.card K * (Fintype.card K + 3) =
      2 * (Fintype.card K + (Fintype.card K + 1).choose 2) := by nlinarith
  rw [symmetricBase, hpoly]
  omega

theorem leftBlock_isSymmetric {α β : Type*} {T : Cubic F α} (hT : Cubic.IsSymmetric T) :
    Cubic.IsSymmetric (Tensor.leftBlock (β := β) T) := by
  have hcore (a : Fin 3 → α) :
      Tensor.leftBlock (β := β) T (fun i => Sum.inl (a i)) = T a := by
    simp only [Tensor.leftBlock, Tensor.vec_three]
  have hdual (x : Fin 3 → α ⊕ β) (i : Fin 3) (b : β) (hi : x i = Sum.inr b) :
      Tensor.leftBlock T x = 0 := by
    fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp_all [Tensor.leftBlock]
  intro σ x
  by_cases hc : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hc
    have hx : x = fun i => Sum.inl (a i) := funext ha
    rw [hx, hcore, hcore]
    exact hT σ a
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    cases hxi : x i with
    | inl a => exact False.elim (hi a hxi)
    | inr b =>
      rw [hdual x i b hxi]
      exact hdual (fun j => x (σ j)) (σ.symm i) b
        (by simpa only [Equiv.apply_symm_apply] using hxi)

theorem directSum_isSymmetric {α β : Type*} {T : Cubic F α} {S : Cubic F β}
    (hT : Cubic.IsSymmetric T) (hS : Cubic.IsSymmetric S) :
    Cubic.IsSymmetric (Tensor.directSum T S) := by
  intro σ x
  change Tensor.leftBlock T (fun i => x (σ i)) +
      Tensor.leftBlock S (fun i => Sum.swap (x (σ i))) =
    Tensor.leftBlock T x + Tensor.leftBlock S (fun i => Sum.swap (x i))
  rw [leftBlock_isSymmetric hT σ x, leftBlock_isSymmetric hS σ (fun i => Sum.swap (x i))]

omit [Field F] in theorem relabel_isSymmetric {α β : Type*} (e : α ≃ β) {T : Cubic F α}
    (hT : Cubic.IsSymmetric T) : Cubic.IsSymmetric (Tensor.relabel (fun _ => e) T) := by
  intro σ x
  exact hT σ (fun i => e.symm (x i))

theorem diagonal_isSymmetric (n : ℕ) :
    Cubic.IsSymmetric (Lemmata.Centroid.Construction.diagonal (F := F) n) := by
  have heq (x : Fin 3 → Fin n) : (x 0 = x 1 ∧ x 1 = x 2) ↔ ∀ i j, x i = x j := by
    constructor
    · intro h i j
      fin_cases i <;> fin_cases j <;> simp_all
    · intro h
      exact ⟨h 0 1, h 1 2⟩
  intro σ x
  simp only [Lemmata.Centroid.Construction.diagonal]
  apply if_congr
  · constructor
    · intro h
      have hall := (heq (fun i => x (σ i))).1 h
      apply (heq x).2
      intro i j
      simpa only [Equiv.apply_symm_apply] using hall (σ.symm i) (σ.symm j)
    · intro h
      have hall := (heq x).1 h
      exact ⟨hall (σ 0) (σ 1), hall (σ 1) (σ 2)⟩
  · rfl
  · rfl

def paddedFull (s : ℕ) : Cubic F (FullCoordinates K ⊕ Fin s) :=
  Tensor.directSum (tensor Finset.univ) (Lemmata.Centroid.Construction.diagonal s)

theorem paddedFull_concise [Nonempty K] (s : ℕ) : Tensor.Concise (paddedFull (F := F) (K := K) s) :=
  full_concise.directSum (Lemmata.Centroid.Construction.diagonal_concise s)

theorem paddedFull_isSymmetric [Nonempty K] (s : ℕ) :
    Cubic.IsSymmetric (paddedFull (F := F) (K := K) s) :=
  directSum_isSymmetric (tensor_isSymmetric Finset.univ) (diagonal_isSymmetric s)

theorem paddedFull_lower_bound [Nonempty K] (s : ℕ) :
    1 + (Fintype.card K + 2).choose 3 + s ≤
      Module.finrank F (Tensor.centroid (paddedFull (F := F) (K := K) s)) := by
  have h₁ := full_centroid_lower_bound (F := F) (K := K)
  have h₂ := Lemmata.Centroid.Construction.diagonal_centroid_lower_bound (F := F) s
  have h₃ := Tensor.finrank_centroid_directSum
    (tensor (F := F) (Finset.univ : Finset (Sym K 2))) (Lemmata.Centroid.Construction.diagonal s)
  exact (Nat.add_le_add h₁ h₂).trans h₃

theorem paddedFull_format (s : ℕ) :
    Fintype.card (FullCoordinates K ⊕ Fin s) =
      symmetricBase (Fintype.card K) + s := by
  rw [Fintype.card_sum, Fintype.card_fin, full_format]

end

end Lemmata.Centroid.Symmetric.Construction
