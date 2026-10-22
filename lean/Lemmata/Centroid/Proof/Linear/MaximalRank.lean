module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Determinant pencils and maximal-rank kernel lifting. -/

open scoped BigOperators Matrix
open Polynomial
open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {F : Type*} [Field F] {α : Type*} [Fintype α]

def borderedIdentity : Matrix (α ⊕ Unit) (α ⊕ Unit) F :=
  Matrix.fromBlocks 1 0 0 0

theorem bordered_pencil_coeff_one (E : Matrix (α ⊕ Unit) (α ⊕ Unit) F) :
    ((borderedIdentity.map C + (X : F[X]) • E.map C).det).coeff 1 =
      E (Sum.inr ()) (Sum.inr ()) := by
  let P : Matrix (α ⊕ Unit) (α ⊕ Unit) F[X] :=
    borderedIdentity.map C + (X : F[X]) • E.map C
  let Q := P.updateRow (Sum.inr ()) (fun j => C (E (Sum.inr ()) j))
  have hfactor : P = Q.updateRow (Sum.inr ()) ((X : F[X]) • Q (Sum.inr ())) := by
    funext i j
    cases i with
    | inl i => simp [Q]
    | inr u =>
      cases u
      cases j with
      | inl j => simp [Q, P, borderedIdentity]
      | inr v => cases v; simp [Q, P, borderedIdentity]
  change P.det.coeff 1 = _
  rw [hfactor, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  simp only [coeff_X_mul]
  rw [coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom (0 : F)) Q.det = _
  rw [RingHom.map_det]
  change (Q.map (Polynomial.evalRingHom (0 : F))).det = _
  have hQ : Q.map (Polynomial.evalRingHom (0 : F)) =
      Matrix.fromBlocks (1 : Matrix α α F) 0
        (fun (_ : Unit) j => E (Sum.inr ()) (Sum.inl j))
        (fun (_ _ : Unit) => E (Sum.inr ()) (Sum.inr ())) := by
    funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Q, P, borderedIdentity, Matrix.fromBlocks]
      | inr v => cases v; simp [Q, P, borderedIdentity, Matrix.fromBlocks]
    | inr u =>
      cases u
      cases j with
      | inl j => simp [Q, Matrix.fromBlocks]
      | inr v => cases v; simp [Q, Matrix.fromBlocks]
  rw [hQ]
  have hd := Matrix.det_fromBlocks_zero₁₂ (1 : Matrix α α F)
      (fun (_ : Unit) j => E (Sum.inr ()) (Sum.inl j))
      (fun (_ _ : Unit) => E (Sum.inr ()) (Sum.inr ()))
  exact hd.trans (by
    simpa only [Matrix.det_one, one_mul] using
      Matrix.det_unique (fun (_ _ : Unit) => E (Sum.inr ()) (Sum.inr ())))

section Independence

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module F W]

theorem independent_line_certificate (v w : ι → W) (hv : LinearIndependent F v) :
    ∃ p : F[X], p.eval 0 = 1 ∧ ∀ t : F, p.eval t ≠ 0 →
      LinearIndependent F (fun i => v i + t • w i) := by
  let f := Fintype.linearCombination F v
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  have hgv (i : ι) : g (v i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa [f, Fintype.linearCombination_apply] using h
  let M : Matrix ι ι F[X] := fun j i => C (g (v i) j) + X * C (g (w i) j)
  have hM (t : F) : M.map (evalRingHom t) =
      (fun j i => g (v i + t • w i) j) := by
    funext j i
    change (evalRingHom t) (M j i) = _
    simp [M]
    ring
  have hzero : M.map (evalRingHom 0) = 1 := by
    rw [hM]
    funext j i
    by_cases h : j = i
    · subst j; simp [hgv]
    · simp [hgv, h]
  refine ⟨M.det, ?_, ?_⟩
  · change evalRingHom (0 : F) M.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hzero, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((M.map (evalRingHom t)).det) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact isUnit_iff_ne_zero.mpr ht
    have hi := (Matrix.linearIndependent_col_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    apply LinearIndependent.of_comp g
    rw [hM] at hi
    exact hi

end Independence

section Kernel

variable {U W : Type*} [AddCommGroup U] [Module F U]
  [AddCommGroup W] [Module F W] [Module.Finite F W] [Infinite F]

theorem maximal_rank_maps_kernel_to_range (f g : U →ₗ[F] W)
    (hmax : ∀ t : F, Module.finrank F (LinearMap.range (f + t • g)) ≤
      Module.finrank F (LinearMap.range f))
    {v : U} (hv : f v = 0) : g v ∈ LinearMap.range f := by
  by_contra hn
  let b := Module.finBasis F (LinearMap.range f)
  choose u hu using fun i => (b i).property
  have hi : LinearIndependent F (fun i => f (u i)) := by
    have hi' := b.linearIndependent.map' (LinearMap.range f).subtype
      (Submodule.ker_subtype _)
    simpa only [hu, Function.comp_def, Submodule.subtype_apply] using hi'
  have hn' : g v ∉ Submodule.span F (Set.range (fun i => f (u i))) := by
    intro h
    apply hn
    exact (Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_range_self f (u i))) h
  let q : Option (Fin (Module.finrank F (LinearMap.range f))) → W :=
    fun i => Option.elim i (g v) (fun j => f (u j))
  let e : Option (Fin (Module.finrank F (LinearMap.range f))) → W :=
    fun i => Option.elim i 0 (fun j => g (u j))
  have hq : LinearIndependent F q := by
    convert hi.option hn' using 1
    funext i
    cases i <;> rfl
  obtain ⟨p, hp, hline⟩ := independent_line_certificate q e hq
  have hp' : p ≠ 0 := by
    intro h
    simp [h] at hp
  obtain ⟨t, hpt, ht⟩ := ((eventually_eval_ne_zero_cofinite hp').and
    (Filter.eventually_cofinite_ne (0 : F))).exists
  let ft := f + t • g
  let z : Option (Fin (Module.finrank F (LinearMap.range f))) → U :=
    fun i => Option.elim i (t⁻¹ • v) u
  have hz (i : Option (Fin (Module.finrank F (LinearMap.range f)))) :
      ft (z i) = q i + t • e i := by
    cases i with
    | none => simp [ft, z, q, e, hv, smul_smul, ht]
    | some i => simp [ft, z, q, e]
  let w : Option (Fin (Module.finrank F (LinearMap.range f))) → LinearMap.range ft :=
    fun i => ⟨ft (z i), LinearMap.mem_range_self ft (z i)⟩
  have hw : LinearIndependent F w := by
    apply LinearIndependent.of_comp (LinearMap.range ft).subtype
    simpa only [Function.comp_def, w, Submodule.subtype_apply, hz] using hline t hpt
  have hcard := hw.fintype_card_le_finrank
  simp only [Fintype.card_option, Fintype.card_fin] at hcard
  have htmax := hmax t
  change Module.finrank F (LinearMap.range ft) ≤ _ at htmax
  omega

end Kernel

section Pivots

variable {ι U W : Type*} [Fintype ι]
  [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
  [Module.Finite F W]

theorem exists_identity_pivot (f : U →ₗ[F] W) :
    ∃ u : Fin (Module.finrank F (LinearMap.range f)) → U,
      ∃ l : W →ₗ[F] (Fin (Module.finrank F (LinearMap.range f)) → F),
        ∀ i, l (f (u i)) = Pi.single i 1 := by
  let b := Module.finBasis F (LinearMap.range f)
  choose u hu using fun i => (b i).property
  have hi : LinearIndependent F (fun i => f (u i)) := by
    have hi' := b.linearIndependent.map' (LinearMap.range f).subtype
      (Submodule.ker_subtype _)
    simpa only [hu, Function.comp_def, Submodule.subtype_apply] using hi'
  let k := Fintype.linearCombination F (fun i => f (u i))
  obtain ⟨l, hl⟩ := k.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi.fintypeLinearCombination_injective)
  refine ⟨u, l, fun i => ?_⟩
  have h := LinearMap.congr_fun hl (Pi.single i 1)
  simpa [k, Fintype.linearCombination_apply] using h

theorem injective_on_range_of_pivot [DecidableEq ι]
    (f : U →ₗ[F] W) (l : W →ₗ[F] (ι → F))
    (u : ι → U) (hdim : Module.finrank F (LinearMap.range f) ≤ Fintype.card ι)
    (hdet : Matrix.det (fun j i => l (f (u i)) j) ≠ 0) :
    Function.Injective (l.comp (LinearMap.range f).subtype) := by
  let M : Matrix ι ι F := fun j i => l (f (u i)) j
  let l' := l.comp (LinearMap.range f).subtype
  have hsurj : Function.Surjective l' := by
    intro y
    obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))) y
    refine ⟨⟨f (∑ i, c i • u i), LinearMap.mem_range_self f _⟩, ?_⟩
    change l (f (∑ i, c i • u i)) = y
    rw [← hc]
    funext j
    simp [M, Matrix.mulVec, dotProduct, mul_comm]
  have hlow := LinearMap.finrank_le_finrank_of_surjective hsurj
  simp only [Module.finrank_fintype_fun_eq_card] at hlow
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank F (LinearMap.range f) = Module.finrank F (ι → F) by
      simpa using le_antisymm hdim hlow)).mpr
  exact hsurj

end Pivots

section PolynomialPencil

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def pencil (A B : Matrix κ ι F) : Matrix κ ι F[X] :=
  A.map C + (X : F[X]) • B.map C

omit [Fintype ι] [Fintype κ] in
theorem eval_pencil (A B : Matrix κ ι F) (t : F) :
    (pencil A B).map (evalRingHom t) = A + t • B := by
  funext i j
  change (evalRingHom t) (pencil A B i j) = _
  simp [pencil]
  ring

theorem polynomial_eq_zero_of_eval_zero_where [Infinite F] {p d : F[X]}
    (hd : d ≠ 0) (h : ∀ t : F, d.eval t ≠ 0 → p.eval t = 0) : p = 0 := by
  have hz : d * p = 0 := Polynomial.zero_of_eval_zero _ (fun t => by
    by_cases ht : d.eval t = 0
    · simp [ht]
    · simp [h t ht])
  exact (mul_eq_zero.mp hz).resolve_left hd


end PolynomialPencil

end Lemmata.Centroid.Linear
