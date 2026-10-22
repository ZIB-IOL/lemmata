module

public import Lemmata.Centroid.Proof.Symmetric.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace Lemmata.Centroid.Symmetric

def orbit {I : Type*} {d : ℕ} (x : Fin d → I) : Sym I d :=
  ⟨(List.ofFn x : Multiset I), by simp⟩

@[simp] theorem orbit_cons {I : Type*} {d : ℕ} (i : I) (x : Fin d → I) :
    orbit (Fin.cons i x) = Sym.cons i (orbit x) := by
  apply Sym.ext
  change (List.ofFn (Fin.cons i x) : Multiset I) = _
  rw [List.ofFn_cons]
  rfl

theorem orbit_permute {I : Type*} {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Fin d → I) :
    orbit (x ∘ σ) = orbit x := by
  apply Sym.ext
  exact Quotient.sound (σ.ofFn_comp_perm x)

theorem orbit_surjective (I : Type*) (d : ℕ) : Function.Surjective (@orbit I d) := by
  induction d with
  | zero => intro s; exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  | succ d ih =>
    intro s
    obtain ⟨i, t, rfl⟩ := Sym.exists_eq_cons_of_succ s
    obtain ⟨x, rfl⟩ := ih t
    exact ⟨Fin.cons i x, orbit_cons i x⟩

theorem orbit_eq_exists_perm {I : Type*} {d : ℕ} {x y : Fin d → I}
    (h : orbit x = orbit y) : ∃ σ : Equiv.Perm (Fin d), y ∘ σ = x := by
  classical
  have hp : (List.ofFn x).Perm (List.ofFn y) := Quotient.exact (congrArg Sym.toMultiset h)
  let e : Fin (List.ofFn x).length ≃ Fin (List.ofFn y).length :=
    Equiv.ofBijective hp.idxBij ⟨hp.idxBij_injective, hp.idxBij_surjective⟩
  let σ : Equiv.Perm (Fin d) :=
    (finCongr (show (List.ofFn x).length = d from List.length_ofFn).symm).trans
      (e.trans (finCongr (show (List.ofFn y).length = d from List.length_ofFn)))
  refine ⟨σ, funext fun i => ?_⟩
  have hget := hp.getElem_idxBij_eq_getElem
    ((finCongr (show (List.ofFn x).length = d from List.length_ofFn).symm) i)
  simp only [List.getElem_ofFn] at hget
  exact hget

abbrev Coefficients (F I : Type*) (d : ℕ) := Sym I d → F

variable {F I : Type*} [Field F]

def toTensor (d : ℕ) : Coefficients F I d →ₗ[F] ((Fin d → I) → F) where
  toFun c x := c (orbit x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem toTensor_apply (d : ℕ) (c : Coefficients F I d) (x : Fin d → I) :
    toTensor d c x = c (orbit x) := rfl

theorem toTensor_injective (d : ℕ) : Function.Injective (@toTensor F I _ d) := by
  intro c c' h
  funext s
  obtain ⟨x, rfl⟩ := orbit_surjective I d s
  exact congrFun h x

def contractCoordinate {d : ℕ} (i : I) :
    Coefficients F I (d + 1) →ₗ[F] Coefficients F I d where
  toFun c s := c (Sym.cons i s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem contractCoordinate_apply {d : ℕ} (i : I)
    (c : Coefficients F I (d + 1)) (s : Sym I d) :
    contractCoordinate i c s = c (Sym.cons i s) := rfl

theorem toTensor_isSymmetric (c : Coefficients F I 3) : Cubic.IsSymmetric (toTensor 3 c) := by
  intro σ x
  exact congrArg c (orbit_permute σ x)

def toSymmetric : Coefficients F I 3 →ₗ[F] ↥(Cubic.symmetricSubmodule (F := F) (I := I)) where
  toFun c := ⟨toTensor 3 c, toTensor_isSymmetric c⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toSymmetric_bijective : Function.Bijective (@toSymmetric F I _) := by
  classical
  constructor
  · intro c c' h
    exact toTensor_injective 3 (congrArg Subtype.val h)
  · intro T
    let representative : Sym I 3 → Fin 3 → I := fun s => Classical.choose (orbit_surjective I 3 s)
    have hrep : ∀ s, orbit (representative s) = s :=
      fun s => Classical.choose_spec (orbit_surjective I 3 s)
    refine ⟨fun s => T.val (representative s), ?_⟩
    apply Subtype.ext
    funext x
    obtain ⟨σ, hσ⟩ := orbit_eq_exists_perm (hrep (orbit x))
    change T.val (representative (orbit x)) = T.val x
    rw [← hσ]
    exact T.property σ x

noncomputable def coordinatesEquiv :
    Coefficients F I 3 ≃ₗ[F] ↥(Cubic.symmetricSubmodule (F := F) (I := I)) :=
  LinearEquiv.ofBijective toSymmetric toSymmetric_bijective

theorem finrank_coefficients [Fintype I] (d : ℕ) :
    Module.finrank F (Coefficients F I d) = (Fintype.card I + d - 1).choose d := by
  classical
  rw [Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose]

theorem finrank_symmetric [Fintype I] :
    Module.finrank F (Cubic.symmetricSubmodule (F := F) (I := I)) =
      (Fintype.card I + 2).choose 3 := by
  rw [← (coordinatesEquiv (F := F) (I := I)).finrank_eq, finrank_coefficients]
  congr 1

variable [Fintype I]

noncomputable def contraction (d : ℕ) (u : I → F) :
    Coefficients F I (d + 1) →ₗ[F] Coefficients F I d :=
  ∑ i, u i • contractCoordinate i

@[simp] theorem contraction_apply (d : ℕ) (u : I → F)
    (c : Coefficients F I (d + 1)) (s : Sym I d) :
    contraction d u c s = ∑ i, u i * c (Sym.cons i s) := by
  simp [contraction, LinearMap.sum_apply, Finset.sum_apply]

@[simp] theorem contraction_delta [DecidableEq I] (d : ℕ) (i : I) :
    contraction d (fun j => if j = i then (1 : F) else 0) = contractCoordinate i := by
  classical
  simp [contraction]

omit [Fintype I] in theorem contractCoordinate_comm {d : ℕ} (i j : I)
    (c : Coefficients F I (d + 2)) :
    contractCoordinate i (contractCoordinate j c) =
      contractCoordinate j (contractCoordinate i c) := by
  funext s
  exact congrArg c (Sym.cons_swap j i s)

def quadraticShadow (S : Submodule F (Coefficients F I 3)) : Submodule F (Coefficients F I 2) :=
  ⨆ i : I, S.map (contractCoordinate i)

def oneSupport (S : Submodule F (Coefficients F I 3)) : Submodule F (Coefficients F I 1) :=
  ⨆ i : I, (quadraticShadow S).map (contractCoordinate i)

noncomputable def doubleShadow (S : Submodule F (Coefficients F I 3)) :
    Submodule F (Coefficients F I 1) :=
  Submodule.span F {v | ∃ u : I → F, ∃ c ∈ S, v = contraction 1 u (contraction 2 u c)}

noncomputable def tripleShadow (S : Submodule F (Coefficients F I 3)) :
    Submodule F (Coefficients F I 0) :=
  Submodule.span F {v | ∃ u : I → F, ∃ c ∈ S,
    v = contraction 0 u (contraction 1 u (contraction 2 u c))}

omit [Fintype I] in theorem contractCoordinate_mem_quadraticShadow (S : Submodule F (Coefficients F I 3))
    (i : I) {c : Coefficients F I 3} (hc : c ∈ S) :
    contractCoordinate i c ∈ quadraticShadow S :=
  Submodule.mem_iSup_of_mem i ⟨c, hc, rfl⟩

theorem contraction_mem_quadraticShadow (S : Submodule F (Coefficients F I 3))
    (u : I → F) {c : Coefficients F I 3} (hc : c ∈ S) :
    contraction 2 u c ∈ quadraticShadow S := by
  classical
  simp only [contraction, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (contractCoordinate_mem_quadraticShadow S i hc)

theorem contraction_mem_oneSupport (S : Submodule F (Coefficients F I 3))
    (u : I → F) {q : Coefficients F I 2} (hq : q ∈ quadraticShadow S) :
    contraction 1 u q ∈ oneSupport S := by
  classical
  simp only [contraction, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ⟨q, hq, rfl⟩)

theorem doubleShadow_le_oneSupport (S : Submodule F (Coefficients F I 3)) :
    doubleShadow S ≤ oneSupport S := by
  apply Submodule.span_le.2
  rintro v ⟨u, c, hc, rfl⟩
  exact contraction_mem_oneSupport S u (contraction_mem_quadraticShadow S u hc)

theorem finrank_tripleShadow_le_one (S : Submodule F (Coefficients F I 3)) :
    Module.finrank F (tripleShadow S) ≤ 1 := by
  have h := Submodule.finrank_le (tripleShadow S)
  simpa [finrank_coefficients] using h

end Lemmata.Centroid.Symmetric
