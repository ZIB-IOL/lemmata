module

public import Lemmata.Centroid.Proof.Symmetric.Coordinates
public import Lemmata.Centroid.Proof.Symmetric.Orbit
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Basis

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.Tensor

variable {F ι : Type*} [Field F] {V : ι → Type*} [∀ i, Fintype (V i)]

theorem contraction_legAction (T : Tensor F ι V) (i : ι)
    (A : Matrix (V i) (V i) F) (u : V i → F) :
    contraction (legAction T i A) i u = contraction T i (A.transpose *ᵥ u) := by
  funext x
  simp only [contraction_apply, legAction_apply, Function.update_self,
    Function.update_idem, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Lemmata.Centroid.Tensor

namespace Lemmata.Centroid.Symmetric

variable {F I : Type*} [Field F] [Fintype I]

omit [Fintype I] in
theorem orbit_update_zero (inst : DecidableEq (Fin 3)) (x : Fin 3 → I) (a : I) :
    orbit (@Function.update (Fin 3) (fun _ => I) inst x 0 a) =
      Sym.cons a (orbit (Fin.tail x)) := by
  have h : @Function.update (Fin 3) (fun _ => I) inst x 0 a = Fin.cons a (Fin.tail x) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
  rw [h, orbit_cons]

def firstContraction (c : Coefficients F I 3) : (I → F) →ₗ[F] Coefficients F I 2 where
  toFun u := contraction 2 u c
  map_add' _ _ := by ext; simp [contraction_apply, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by ext; simp [contraction_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem firstContraction_apply (c : Coefficients F I 3) (u : I → F) :
    firstContraction c u = contraction 2 u c := rfl

theorem firstContraction_toTensor (c : Coefficients F I 3) (u : I → F) (x : Fin 3 → I) :
    toTensor 2 (firstContraction c u) (Fin.tail x) =
      Tensor.contraction (toTensor 3 c) 0 u x := by
  simp only [toTensor_apply, firstContraction_apply, contraction_apply, Tensor.contraction_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  exact (orbit_update_zero (Classical.decEq _) x a).symm

theorem firstContraction_injective {c : Coefficients F I 3}
    (hc : Tensor.Concise (toTensor 3 c)) : Function.Injective (firstContraction c) := by
  intro u v h
  apply hc 0
  funext x
  rw [← firstContraction_toTensor, ← firstContraction_toTensor, h]

namespace CentroidModel

variable (c : Coefficients F I 3) (hc : Tensor.Concise (toTensor 3 c))

abbrev Algebra := Tensor.centroidAlgebra (toTensor 3 c) hc

def representation : Algebra c hc →ₐ[F] Module.End F (I → F) :=
  Tensor.centroidDualRepresentation (toTensor 3 c) hc 0

theorem representation_apply (a : Algebra c hc) (u : I → F) :
    representation c hc a u = (a.val 0).transpose *ᵥ u := rfl

theorem representation_injective : Function.Injective (representation c hc) :=
  Tensor.centroidDualRepresentation_injective hc 0

def actionTensor : Algebra c hc →ₗ[F] Cubic.symmetricSubmodule (F := F) (I := I) where
  toFun a := ⟨Tensor.legAction (toTensor 3 c) 0 (a.val 0),
    Cubic.centroid_action_isSymmetric hc (toTensor_isSymmetric c) a.property⟩
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

def action : Algebra c hc →ₗ[F] Coefficients F I 3 :=
  (coordinatesEquiv (F := F) (I := I)).symm.toLinearMap.comp (actionTensor c hc)

theorem toTensor_action (a : Algebra c hc) :
    toTensor 3 (action c hc a) = Tensor.legAction (toTensor 3 c) 0 (a.val 0) := by
  change (coordinatesEquiv ((coordinatesEquiv (F := F) (I := I)).symm
    (actionTensor c hc a))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem action_injective : Function.Injective (action c hc) := by
  intro a b h
  apply Tensor.centroidProjectionAlgHom_injective hc 0
  change a.val 0 = b.val 0
  apply Tensor.legAction_injective hc 0
  rw [← toTensor_action, ← toTensor_action, h]

theorem contraction_action (u : I → F) (a : Algebra c hc) :
    contraction 2 u (action c hc a) = firstContraction c (representation c hc a u) := by
  apply toTensor_injective 2
  funext x
  let y : Fin 3 → I := Fin.cons (x 0) x
  have hleft := firstContraction_toTensor (action c hc a) u y
  have hright := firstContraction_toTensor c (representation c hc a u) y
  rw [representation_apply] at hright
  calc
    _ = Tensor.contraction (toTensor 3 (action c hc a)) 0 u y := by
      simpa [y, firstContraction] using hleft
    _ = Tensor.contraction (Tensor.legAction (toTensor 3 c) 0 (a.val 0)) 0 u y := by
      rw [toTensor_action]
    _ = Tensor.contraction (toTensor 3 c) 0 ((a.val 0).transpose *ᵥ u) y :=
      congrFun (Tensor.contraction_legAction (toTensor 3 c) 0 (a.val 0) u) y
    _ = _ := by simpa [y, representation_apply] using hright.symm

theorem finrank_algebra :
    Module.finrank F (Algebra c hc) = Module.finrank F (Tensor.centroid (toTensor 3 c)) :=
  (Tensor.centroidAlgebra (toTensor 3 c) hc).toSubmoduleEquiv.finrank_eq

theorem contracted_image (P : Submodule F (Algebra c hc)) (u : I → F) :
    (P.map (action c hc)).map (contraction 2 u) =
      (P.map (evaluation (representation c hc) u)).map (firstContraction c) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro a
  exact contraction_action c hc u a

theorem finrank_contracted_image (P : Submodule F (Algebra c hc)) (u : I → F) :
    Module.finrank F ((P.map (action c hc)).map (contraction 2 u)) =
      Module.finrank F ((evaluation (representation c hc) u).domRestrict P).range := by
  rw [contracted_image, LinearMap.range_domRestrict]
  exact (Submodule.equivMapOfInjective (firstContraction c)
    (firstContraction_injective hc) _).finrank_eq.symm

def idealImage (v : I → F) : Submodule F (Coefficients F I 3) :=
  ((orbitIdeal (representation c hc) v).restrictScalars F).map (action c hc)

def hyperplaneImage (ℓ : Algebra c hc →ₗ[F] F) : Submodule F (Coefficients F I 3) :=
  ℓ.ker.map (action c hc)

theorem idealImage_le_contraction_ker (v : I → F) :
    idealImage c hc v ≤ (contraction 2 v).ker := by
  rintro _ ⟨a, ha, rfl⟩
  change contraction 2 v (action c hc a) = 0
  rw [contraction_action]
  change representation c hc a v = 0 at ha
  rw [ha, map_zero]

theorem finrank_idealImage (v : I → F) :
    Module.finrank F (idealImage c hc v) =
      Module.finrank F ((orbitIdeal (representation c hc) v).restrictScalars F) :=
  (Submodule.equivMapOfInjective (action c hc) (action_injective c hc) _).finrank_eq.symm

theorem dimension_identity (v : I → F) :
    Module.finrank F (Tensor.centroid (toTensor 3 c)) =
      Module.finrank F (evaluation (representation c hc) v).range +
        Module.finrank F (idealImage c hc v) := by
  rw [finrank_idealImage, ← finrank_algebra c hc]
  exact (orbit_dimension_identity (representation c hc) v).symm

end CentroidModel

def onePairing (u : I → F) : Coefficients F I 1 →ₗ[F] F where
  toFun r := ∑ i, u i * r (Sym.oneEquiv i)
  map_add' r s := by
    change (∑ i, u i * (r (Sym.oneEquiv i) + s (Sym.oneEquiv i))) = _
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' t r := by
    change (∑ i, u i * (t * r (Sym.oneEquiv i))) = t * ∑ i, u i * r (Sym.oneEquiv i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def oneDual : (I → F) →ₗ[F] Module.Dual F (Coefficients F I 1) where
  toFun := onePairing
  map_add' u v := by ext r; simp [onePairing, add_mul, Finset.sum_add_distrib]
  map_smul' t u := by ext r; simp [onePairing, Finset.mul_sum, mul_assoc]

theorem oneDual_injective : Function.Injective (oneDual (F := F) (I := I)) := by
  classical
  intro u v h
  funext i
  have hi := congrArg (fun f : Module.Dual F (Coefficients F I 1) =>
    f (fun s => if s = Sym.oneEquiv i then 1 else 0)) h
  change (∑ x, u x * if Sym.oneEquiv x = Sym.oneEquiv i then 1 else 0) =
    ∑ x, v x * if Sym.oneEquiv x = Sym.oneEquiv i then 1 else 0 at hi
  simpa only [Sym.oneEquiv.injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hi

theorem onePairing_oneSupport {S : Submodule F (Coefficients F I 3)} {u : I → F}
    (hkill : ∀ c ∈ S, contraction 2 u c = 0) :
    oneSupport S ≤ (onePairing u).ker := by
  classical
  apply iSup_le
  intro i
  rintro r ⟨q, hq, rfl⟩
  have hquad : quadraticShadow S ≤ ((onePairing u).comp (contractCoordinate i)).ker := by
    apply iSup_le
    intro j
    rintro _ ⟨c, hc, rfl⟩
    change ∑ k, u k * c (Sym.cons j (Sym.cons i (Sym.oneEquiv k))) = 0
    have h := congrFun (hkill c hc) (Sym.cons i (Sym.cons j Sym.nil))
    simp only [contraction_apply, Pi.zero_apply] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k _
    congr 2
    rw [Sym.cons_swap k i, Sym.cons_swap k j, Sym.cons_swap i j]
    rfl
  exact hquad hq

theorem oneSupport_dimension_bound (P : Submodule F (I → F))
    (S : Submodule F (Coefficients F I 3))
    (hkill : ∀ u ∈ P, ∀ c ∈ S, contraction 2 u c = 0) :
    Module.finrank F P + Module.finrank F (oneSupport S) ≤ Fintype.card I := by
  classical
  have hle : P.map oneDual ≤ (oneSupport S).dualAnnihilator := by
    rintro _ ⟨u, hu, rfl⟩
    apply (Submodule.mem_dualAnnihilator _).2
    intro r hr
    exact onePairing_oneSupport (hkill u hu) hr
  have hdim := Submodule.finrank_mono hle
  have heq := (Submodule.equivMapOfInjective (oneDual (F := F) (I := I))
    oneDual_injective P).finrank_eq
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (oneSupport S)
  have hcard : Module.finrank F (Coefficients F I 1) = Fintype.card I := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Sym.oneEquiv.symm
  omega

namespace CentroidModel

variable (c : Coefficients F I 3) (hc : Tensor.Concise (toTensor 3 c))

include hc in
theorem exists_reduction [Infinite F] [Nonempty I] :
    ∃ (m : ℕ) (E S : Submodule F (Coefficients F I 3)) (v : I → F),
      Module.finrank F (Tensor.centroid (toTensor 3 c)) = m + Module.finrank F S ∧
      m + Module.finrank F (oneSupport S) ≤ Fintype.card I ∧
      S ≤ E ∧ S ≤ (contraction 2 v).ker ∧
      (∀ w : I → F, Module.finrank F (E.map (contraction 2 w)) ≤
        Module.finrank F (E.map (contraction 2 v))) ∧
      Module.finrank F (E.map (contraction 2 v)) + 1 ≤ m := by
  classical
  let ρ := representation c hc
  have : Nontrivial (Algebra c hc) := ρ.toRingHom.domain_nontrivial
  obtain ⟨v, hv⟩ := exists_maximal_orbit ρ
  obtain ⟨ℓ, hℓ, hnil⟩ := exists_nilpotent_hyperplane (F := F) (A := Algebra c hc)
  let E := hyperplaneImage c hc ℓ
  let S := idealImage c hc v
  let m := Module.finrank F (evaluation ρ v).range
  have hSE : S ≤ E := by
    apply Submodule.map_mono
    intro a ha
    apply hnil
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact orbitIdeal_mul_eq_zero ρ (representation_injective c hc) hv ha ha
  have hsupport : m + Module.finrank F (oneSupport S) ≤ Fintype.card I := by
    apply oneSupport_dimension_bound (evaluation ρ v).range S
    intro u hu r hr
    obtain ⟨a, ha, rfl⟩ := hr
    rw [contraction_action]
    have hz := orbitIdeal_kills_orbit ρ ha hu
    rw [hz, map_zero]
  have hrank : Module.finrank F (E.map (contraction 2 v)) + 1 = m := by
    change Module.finrank F ((ℓ.ker.map (action c hc)).map (contraction 2 v)) + 1 = _
    rw [finrank_contracted_image]
    exact maximal_orbit_hyperplane_rank ρ (representation_injective c hc) ℓ hℓ hnil hv
  refine ⟨m, E, S, v, dimension_identity c hc v, hsupport, hSE,
    idealImage_le_contraction_ker c hc v, ?_, hrank.le⟩
  intro w
  change Module.finrank F ((ℓ.ker.map (action c hc)).map (contraction 2 w)) ≤
    Module.finrank F ((ℓ.ker.map (action c hc)).map (contraction 2 v))
  rw [finrank_contracted_image, finrank_contracted_image]
  exact maximal_orbit_hyperplane_is_max ρ (representation_injective c hc) ℓ hℓ hnil hv w

end CentroidModel

end Lemmata.Centroid.Symmetric
