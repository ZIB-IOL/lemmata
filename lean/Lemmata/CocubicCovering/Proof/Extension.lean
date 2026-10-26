module

public import Lemmata.CocubicCovering.Proof.Bound
public meta import Lemmata.CocubicCovering.Proof.Bound
public import Lemmata.CocubicCovering.Proof.Forms
public meta import Lemmata.CocubicCovering.Proof.Forms
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.CoveringExtension

open Covering Module
open scoped BigOperators

def oldPoint {m : ℕ} (z : Vector (m + 3)) : Vector m := fun i => z (Fin.castAdd 3 i)
def newPoint {m : ℕ} (z : Vector (m + 3)) : Vector 3 := fun i => z (Fin.natAdd m i)

@[simp] theorem oldPoint_append {m : ℕ} (x : Vector m) (y : Vector 3) :
    oldPoint (Fin.append x y) = x := by funext i; exact Fin.append_left x y i

@[simp] theorem newPoint_append {m : ℕ} (x : Vector m) (y : Vector 3) :
    newPoint (Fin.append x y) = y := by funext i; exact Fin.append_right x y i

def pointEquiv (m : ℕ) : Vector m × Vector 3 ≃ Vector (m + 3) where
  toFun p := Fin.append p.1 p.2
  invFun z := (oldPoint z, newPoint z)
  left_inv p := by rcases p with ⟨x, y⟩; simp
  right_inv z := Fin.append_castAdd_natAdd

def monomialEquiv (m : ℕ) :
    (Finset (Fin m) × Finset (Fin 3)) ≃ Finset (Fin (m + 3)) :=
  (Finset.sumEquiv (α := Fin m) (β := Fin 3)).toEquiv.symm.trans
    (Equiv.finsetCongr (finSumFinEquiv : Fin m ⊕ Fin 3 ≃ Fin (m + 3)))

@[simp] theorem monomialEquiv_card {m : ℕ} (s : Finset (Fin m)) (t : Finset (Fin 3)) :
    (monomialEquiv m (s, t)).card = s.card + t.card := by
  change ((s.disjSum t).map finSumFinEquiv.toEmbedding).card = _
  simp

theorem monomial_split {m : ℕ} (s : Finset (Fin m)) (t : Finset (Fin 3))
    (z : Vector (m + 3)) :
    monomial (monomialEquiv m (s, t)) z =
      monomial s (oldPoint z) * monomial t (newPoint z) := by
  change (∏ i : Fin (m + 3), if i ∈ (s.disjSum t).map finSumFinEquiv.toEmbedding
      then z i else 1) =
    (∏ i : Fin m, if i ∈ s then z (Fin.castAdd 3 i) else 1) *
      ∏ i : Fin 3, if i ∈ t then z (Fin.natAdd m i) else 1
  rw [Fin.prod_univ_add]
  simp only [Finset.mem_map_equiv, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]

def liftLinear (m : ℕ) : BooleanFunction m →ₗ[Field] BooleanFunction (m + 3) where
  toFun f z := f (oldPoint z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftANF {m : ℕ} (p : ANF m) : ANF (m + 3) :=
  fun u => let st := (monomialEquiv m).symm u
    if st.2 = ∅ then p st.1 else 0

def extractANF {m : ℕ} (p : ANF (m + 3)) : ANF m :=
  fun s => p (monomialEquiv m (s, Finset.univ))

theorem liftANF_degree {m r : ℕ} {p : ANF m} (hp : DegreeLE p r) :
    DegreeLE (liftANF p) r := by
  intro u hu
  obtain ⟨⟨s, t⟩, rfl⟩ := (monomialEquiv m).surjective u
  rw [monomialEquiv_card] at hu
  simp only [liftANF, Equiv.symm_apply_apply]
  by_cases ht : t = ∅
  · subst t
    simpa using hp s (by simpa using hu)
  · simp [ht]

theorem extractANF_degree {m r : ℕ} {p : ANF (m + 3)}
    (hp : DegreeLE p (r + 3)) : DegreeLE (extractANF p) r := by
  intro s hs
  apply hp
  rw [monomialEquiv_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem eval_split {m : ℕ} (p : ANF (m + 3)) (x : Vector m) (y : Vector 3) :
    eval p (Fin.append x y) =
      ∑ s : Finset (Fin m), ∑ t : Finset (Fin 3),
        p (monomialEquiv m (s, t)) * monomial s x * monomial t y := by
  calc
    eval p (Fin.append x y) = ∑ st : Finset (Fin m) × Finset (Fin 3),
        p (monomialEquiv m st) * monomial (monomialEquiv m st) (Fin.append x y) :=
      ((monomialEquiv m).sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [monomial_split, oldPoint_append, newPoint_append, mul_assoc]

@[simp] theorem eval_liftANF_append {m : ℕ} (p : ANF m) (x : Vector m) (y : Vector 3) :
    eval (liftANF p) (Fin.append x y) = eval p x := by
  rw [eval_split]
  simp [liftANF, eval, ite_mul, monomial]

theorem eval_liftANF {m : ℕ} (p : ANF m) : eval (liftANF p) = liftLinear m (eval p) := by
  funext z
  obtain ⟨⟨x, y⟩, rfl⟩ := (pointEquiv m).surjective z
  change eval (liftANF p) (Fin.append x y) = eval p (oldPoint (Fin.append x y))
  rw [oldPoint_append]
  exact eval_liftANF_append p x y

theorem lift_reedMuller {m r : ℕ} {f : BooleanFunction m} (hf : f ∈ reedMuller m r) :
    liftLinear m f ∈ reedMuller (m + 3) r := by
  obtain ⟨p, hp, rfl⟩ := mem_reedMuller_iff.mp hf
  exact mem_reedMuller_iff.mpr ⟨liftANF p, liftANF_degree hp, eval_liftANF p⟩

theorem eval_extractANF {m : ℕ} (p : ANF (m + 3)) (x : Vector m) :
    (∑ y : Vector 3, eval p (Fin.append x y)) = eval (extractANF p) x := by
  calc
    (∑ y : Vector 3, eval p (Fin.append x y)) =
        ∑ s : Finset (Fin m), ∑ t : Finset (Fin 3),
          (p (monomialEquiv m (s, t)) * monomial s x) *
            (∑ y : Vector 3, monomial t y) := by
      simp_rw [eval_split]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = eval (extractANF p) x := by simp [sum_monomial, extractANF, eval]

@[simp] theorem liftLinear_append {m : ℕ} (f : BooleanFunction m)
    (x : Vector m) (y : Vector 3) : liftLinear m f (Fin.append x y) = f x := by
  change f (oldPoint (Fin.append x y)) = f x
  rw [oldPoint_append]

def newCube (m : ℕ) : BooleanFunction (m + 3) :=
  monomial (monomialEquiv m (∅, Finset.univ))

def extendedFunction {m : ℕ} (f : BooleanFunction m) : BooleanFunction (m + 3) :=
  newCube m * liftLinear m f + liftLinear m (monomial Finset.univ)

@[simp] theorem extendedFunction_append {m : ℕ} (f : BooleanFunction m)
    (x : Vector m) (y : Vector 3) :
    extendedFunction f (Fin.append x y) =
      monomial Finset.univ y * f x + monomial Finset.univ x := by
  simp only [extendedFunction, Pi.mul_apply, Pi.add_apply, newCube,
    monomial_split, oldPoint_append, newPoint_append, liftLinear_append]
  simp [monomial]

def sumNew {m : ℕ} (h : BooleanFunction (m + 3)) : BooleanFunction m :=
  fun x => ∑ y : Vector 3, h (Fin.append x y)

private theorem sum_const_three (a : Field) : (∑ _y : Vector 3, a) = 0 := by
  have hone : (∑ _y : Vector 3, (1 : Field)) = 0 := by native_decide
  calc
    (∑ _y : Vector 3, a) = (∑ _y : Vector 3, (1 : Field)) * a := by
      rw [Finset.sum_mul]
      simp
    _ = 0 := by rw [hone, zero_mul]

theorem sumNew_extendedFunction {m : ℕ} (f : BooleanFunction m)
    (h : BooleanFunction (m + 3)) : sumNew (extendedFunction f + h) = f + sumNew h := by
  funext x
  change (∑ y : Vector 3, (extendedFunction f (Fin.append x y) + h (Fin.append x y))) =
    f x + (∑ y : Vector 3, h (Fin.append x y))
  simp_rw [extendedFunction_append]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_monomial]
  rw [sum_const_three]
  simp

theorem sumNew_reedMuller {m : ℕ} (hm : 4 ≤ m)
    {h : BooleanFunction (m + 3)} (hh : h ∈ reedMuller (m + 3) (m - 1)) :
    sumNew h ∈ reedMuller m (m - 4) := by
  obtain ⟨p, hp, rfl⟩ := mem_reedMuller_iff.mp hh
  have he : sumNew (eval p) = eval (extractANF p) := by
    funext x
    exact eval_extractANF p x
  rw [he]
  refine mem_reedMuller_iff.mpr ⟨extractANF p, extractANF_degree ?_, rfl⟩
  simpa only [show m - 4 + 3 = m - 1 by omega] using hp

theorem newCube_mem (m : ℕ) : newCube m ∈ reedMuller (m + 3) 3 := by
  apply monomial_mem_reedMuller
  simp

theorem oldFull_mem (m : ℕ) :
    liftLinear m (monomial Finset.univ) ∈ reedMuller (m + 3) m :=
  lift_reedMuller (monomial_mem_reedMuller Finset.univ (by simp))

theorem extendedFunction_mem {m : ℕ} (hm : 3 ≤ m) {f : BooleanFunction m}
    (hf : f ∈ reedMuller m (m - 3)) : extendedFunction f ∈ reedMuller (m + 3) m := by
  apply (reedMuller (m + 3) m).add_mem
  · exact reedMuller_mono (by omega) (reedMuller_mul (newCube_mem m) (lift_reedMuller hf))
  · exact oldFull_mem m

theorem degreeLE_card {m : ℕ} (p : ANF m) : DegreeLE p m := by
  intro s hs
  have hc := Finset.card_le_univ s
  simp only [Fintype.card_fin] at hc
  omega

theorem reedMuller_cap {m r : ℕ} {f : BooleanFunction m} (hf : f ∈ reedMuller m r) :
    f ∈ reedMuller m m := by
  obtain ⟨p, hp, rfl⟩ := mem_reedMuller_iff.mp hf
  exact mem_reedMuller_iff.mpr ⟨p, degreeLE_card p, rfl⟩

theorem lifted_admissibility {m : ℕ} (hm : 2 ≤ m) {f q : BooleanFunction m}
    (hq : q ∈ reedMuller m 2) (hproduct : q * f ∈ reedMuller m (m - 2)) :
    liftLinear m q * extendedFunction f ∈ reedMuller (m + 3) (m + 1) := by
  have he : liftLinear m q * extendedFunction f =
      newCube m * liftLinear m (q * f) +
        liftLinear m (q * monomial Finset.univ) := by
    funext z
    change q (oldPoint z) *
        (newCube m z * f (oldPoint z) + monomial Finset.univ (oldPoint z)) =
      newCube m z * (q (oldPoint z) * f (oldPoint z)) +
        q (oldPoint z) * monomial Finset.univ (oldPoint z)
    ring
  rw [he]
  apply (reedMuller (m + 3) (m + 1)).add_mem
  · exact reedMuller_mono (by omega)
      (reedMuller_mul (newCube_mem m) (lift_reedMuller hproduct))
  · apply reedMuller_mono (Nat.le_succ m)
    apply lift_reedMuller
    apply reedMuller_cap
    exact reedMuller_mul hq (monomial_mem_reedMuller (r := m) Finset.univ (by simp))

variable {Q : Type*} [AddCommGroup Q] [Module Field Q]

theorem lifted_supportGram {m : ℕ} (f : BooleanFunction m)
    (h : BooleanFunction (m + 3)) (e : Q →ₗ[Field] BooleanFunction m) :
    supportGram (extendedFunction f + h) ((liftLinear m).comp e) =
      supportGram (f + sumNew h) e := by
  ext q q'
  rw [supportGram_apply, supportGram_apply]
  rw [← (pointEquiv m).sum_comp (fun z =>
    (((liftLinear m).comp e) q) z * (((liftLinear m).comp e) q') z *
      (extendedFunction f + h) z), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  change (∑ y : Vector 3, liftLinear m (e q) (Fin.append x y) *
      liftLinear m (e q') (Fin.append x y) *
      (extendedFunction f + h) (Fin.append x y)) = _
  simp only [liftLinear_append]
  rw [← Finset.mul_sum]
  change (e q x * e q' x) * sumNew (extendedFunction f + h) x = _
  rw [sumNew_extendedFunction]

theorem rank_bound_lift {m r : ℕ} (hm : 4 ≤ m) (f : BooleanFunction m)
    (e : Q →ₗ[Field] BooleanFunction m)
    (hbound : ∀ p ∈ reedMuller m (m - 4),
      r ≤ finrank Field (LinearMap.range (supportGram (f + p) e)))
    (h : BooleanFunction (m + 3)) (hh : h ∈ reedMuller (m + 3) (m - 1)) :
    r ≤ finrank Field (LinearMap.range
      (supportGram (extendedFunction f + h) ((liftLinear m).comp e))) := by
  rw [lifted_supportGram]
  exact hbound (sumNew h) (sumNew_reedMuller hm hh)

@[simp] theorem newCube_append {m : ℕ} (x : Vector m) (y : Vector 3) :
    newCube m (Fin.append x y) = monomial Finset.univ y := by
  simp only [newCube, monomial_split, oldPoint_append, newPoint_append]
  simp [monomial]

def newPair (m : ℕ) (j : Fin 3) : BooleanFunction (m + 3) :=
  monomial (monomialEquiv m (∅, Finset.univ.erase j))

@[simp] theorem newPair_append {m : ℕ} (j : Fin 3) (x : Vector m) (y : Vector 3) :
    newPair m j (Fin.append x y) = monomial (Finset.univ.erase j) y := by
  simp only [newPair, monomial_split, oldPoint_append, newPoint_append]
  simp [monomial]

theorem newPair_mem (m : ℕ) (j : Fin 3) : newPair m j ∈ reedMuller (m + 3) 2 := by
  apply monomial_mem_reedMuller
  simp

theorem newPair_mul_newCube (m : ℕ) (j : Fin 3) : newPair m j * newCube m = newCube m := by
  funext z
  obtain ⟨⟨x, y⟩, rfl⟩ := (pointEquiv m).surjective z
  change newPair m j (Fin.append x y) * newCube m (Fin.append x y) =
    newCube m (Fin.append x y)
  rw [newPair_append, newCube_append, ← monomial_union,
    Finset.union_eq_right.mpr (Finset.erase_subset j Finset.univ)]

theorem affine_append {m : ℕ} (a : Field × Vector (m + 3)) (x : Vector m) (y : Vector 3) :
    affineFunctionLinear (m + 3) a (Fin.append x y) =
      affineFunctionLinear m (a.1, oldPoint a.2) x + ∑ j, newPoint a.2 j * y j := by
  simp only [affineFunctionLinear_apply]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, oldPoint, newPoint]
  ring

private theorem three_pair_moment : ∀ (a : Field) (b : Vector 3) (j : Fin 3),
    (∑ y : Vector 3, (a + ∑ i, b i * y i) * monomial (Finset.univ.erase j) y) = b j := by
  native_decide

theorem newPair_affine_oldFull {m : ℕ} (a : Field × Vector (m + 3)) (j : Fin 3) :
    (∑ z : Vector (m + 3), affineFunctionLinear (m + 3) a z * newPair m j z *
      liftLinear m (monomial Finset.univ) z) = newPoint a.2 j := by
  rw [← (pointEquiv m).sum_comp (fun z =>
    affineFunctionLinear (m + 3) a z * newPair m j z *
      liftLinear m (monomial Finset.univ) z), Fintype.sum_prod_type]
  change (∑ x : Vector m, ∑ y : Vector 3,
    affineFunctionLinear (m + 3) a (Fin.append x y) * newPair m j (Fin.append x y) *
      liftLinear m (monomial Finset.univ) (Fin.append x y)) = _
  simp only [affine_append, newPair_append, liftLinear_append]
  simp_rw [← Finset.sum_mul, three_pair_moment]
  rw [← Finset.mul_sum, sum_monomial]
  simp

theorem newPair_affine_moment {m : ℕ} (hm : 4 ≤ m) (f : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3)) (h : BooleanFunction (m + 3))
    (hh : h ∈ reedMuller (m + 3) (m - 1)) (a : Field × Vector (m + 3)) (j : Fin 3) :
    (∑ z : Vector (m + 3), affineFunctionLinear (m + 3) a z * newPair m j z *
      (extendedFunction f + h) z) = newPoint a.2 j := by
  let A := affineFunctionLinear (m + 3) a
  have hcorrection : (∑ z : Vector (m + 3), (A * newPair m j) z * h z) = 0 :=
    sum_mul_reedMuller_eq_zero (reedMuller_mul (affineFunction_mem a) (newPair_mem m j))
      hh (by omega)
  change (∑ z : Vector (m + 3), (A * newPair m j * h) z) = 0 at hcorrection
  have hfirst : (∑ z : Vector (m + 3),
      (A * newPair m j * (newCube m * liftLinear m f)) z) = 0 := by
    have he : A * newPair m j * (newCube m * liftLinear m f) =
        A * (newCube m * liftLinear m f) := by
      calc
        _ = A * (newPair m j * newCube m) * liftLinear m f := by ring
        _ = _ := by rw [newPair_mul_newCube]; ring
    rw [he]
    exact sum_reedMuller_eq_zero
      (reedMuller_mul (affineFunction_mem a)
        (reedMuller_mul (newCube_mem m) (lift_reedMuller hf))) (by omega)
  have he : A * newPair m j * (extendedFunction f + h) =
      A * newPair m j * (newCube m * liftLinear m f) +
        A * newPair m j * liftLinear m (monomial Finset.univ) + A * newPair m j * h := by
    rw [extendedFunction]
    ring
  change (∑ z : Vector (m + 3), (A * newPair m j * (extendedFunction f + h)) z) = _
  rw [he]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [hfirst, hcorrection]
  simpa only [zero_add, add_zero, Pi.mul_apply] using newPair_affine_oldFull a j

theorem affineSupport_injective_lift {m : ℕ} (hm : 4 ≤ m) (f : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3))
    (hinjective : ∀ p ∈ reedMuller m (m - 4),
      Function.Injective ((restrictSupport (f + p)).comp (affineFunctionLinear m)))
    (h : BooleanFunction (m + 3)) (hh : h ∈ reedMuller (m + 3) (m - 1)) :
    Function.Injective ((restrictSupport (extendedFunction f + h)).comp
      (affineFunctionLinear (m + 3))) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  have hpoint : ∀ z : Vector (m + 3),
      affineFunctionLinear (m + 3) a z * (extendedFunction f + h) z = 0 := by
    intro z
    by_cases hz : (extendedFunction f + h) z = 0
    · simp [hz]
    · have hz' := congrFun ha (⟨z, hz⟩ : Support (extendedFunction f + h))
      change affineFunctionLinear (m + 3) a z = 0 at hz'
      rw [hz', zero_mul]
  have hnew : newPoint a.2 = 0 := by
    funext j
    have hmom := newPair_affine_moment hm f hf h hh a j
    have hz : (∑ z : Vector (m + 3), affineFunctionLinear (m + 3) a z * newPair m j z *
        (extendedFunction f + h) z) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      rw [mul_right_comm, hpoint z, zero_mul]
    exact hmom.symm.trans hz
  let old : Field × Vector m := (a.1, oldPoint a.2)
  have haff : ∀ x : Vector m, ∀ y : Vector 3,
      affineFunctionLinear (m + 3) a (Fin.append x y) = affineFunctionLinear m old x := by
    intro x y
    rw [affine_append, hnew]
    simp [old]
  have holdpoint : ∀ x : Vector m,
      affineFunctionLinear m old x * (f + sumNew h) x = 0 := by
    intro x
    have hz : (∑ y : Vector 3, affineFunctionLinear (m + 3) a (Fin.append x y) *
        (extendedFunction f + h) (Fin.append x y)) = 0 :=
      Finset.sum_eq_zero fun y _ => hpoint (Fin.append x y)
    simp_rw [haff] at hz
    rw [← Finset.mul_sum] at hz
    change affineFunctionLinear m old x * sumNew (extendedFunction f + h) x = 0 at hz
    rw [sumNew_extendedFunction] at hz
    exact hz
  have holdmap : ((restrictSupport (f + sumNew h)).comp (affineFunctionLinear m)) old = 0 := by
    funext x
    change affineFunctionLinear m old x = 0
    exact (mul_eq_zero.mp (holdpoint x.val)).resolve_right x.property
  have hold : old = 0 := by
    apply hinjective (sumNew h) (sumNew_reedMuller hm hh)
    simpa only [map_zero] using holdmap
  have hconst : a.1 = 0 := congrArg Prod.fst hold
  have holdcoefficients : oldPoint a.2 = 0 := congrArg Prod.snd hold
  have hlinear : a.2 = 0 := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact congrFun holdcoefficients j
    · intro j
      exact congrFun hnew j
  exact Prod.ext hconst hlinear

theorem affineOnSupport_finrank_of_injective {m : ℕ} (g : BooleanFunction m)
    (hinjective : Function.Injective ((restrictSupport g).comp (affineFunctionLinear m))) :
    m + 1 ≤ finrank Field (affineOnSupport g) := by
  let e := (restrictSupport g).comp (affineFunctionLinear m)
  let e' := e.codRestrict (affineOnSupport g) fun a =>
    ⟨affineFunctionLinear m a, affineFunction_mem a, rfl⟩
  have he : Function.Injective e' := by
    intro a b hab
    exact hinjective (congrArg Subtype.val hab)
  have hd := LinearMap.finrank_le_finrank_of_injective he
  simpa only [Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_comm] using hd

theorem affineOnSupport_finrank_lift {m : ℕ} (hm : 4 ≤ m) (f : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3))
    (hinjective : ∀ p ∈ reedMuller m (m - 4),
      Function.Injective ((restrictSupport (f + p)).comp (affineFunctionLinear m)))
    (h : BooleanFunction (m + 3)) (hh : h ∈ reedMuller (m + 3) (m - 1)) :
    m + 4 ≤ finrank Field (affineOnSupport (extendedFunction f + h)) := by
  exact affineOnSupport_finrank_of_injective _ (affineSupport_injective_lift hm f hf hinjective h hh)

end Lemmata.CocubicCovering.CoveringExtension
