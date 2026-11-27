module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

open scoped BigOperators

open Classical

noncomputable section

namespace Lemmata.Centroid.Linear

variable {A : Type*} [CommRing A]

theorem local_quotient_maximal_power (m : Ideal A) [m.IsMaximal]
    (n : ℕ) (hn : 0 < n) : IsLocalRing (A ⧸ m ^ n) := by
  have hker : RingHom.ker (Ideal.Quotient.mk (m ^ n)) ≤ m := by
    rw [Ideal.mk_ker]
    exact Ideal.pow_le_self hn.ne'
  have hmax : (m.map (Ideal.Quotient.mk (m ^ n))).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  have hrad : m.map (Ideal.Quotient.mk (m ^ n)) = nilradical (A ⧸ m ^ n) := by
    have h := Ideal.map_radical_of_surjective (f := Ideal.Quotient.mk (m ^ n))
      Ideal.Quotient.mk_surjective (show RingHom.ker (Ideal.Quotient.mk (m ^ n)) ≤ m ^ n by
        rw [Ideal.mk_ker])
    rw [Ideal.radical_pow m hn.ne', (Ideal.IsPrime.isRadical inferInstance).radical,
      Ideal.map_quotient_self] at h
    exact h
  let : (nilradical (A ⧸ m ^ n)).IsMaximal := hrad ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical _

def localExponent (A : Type*) [CommRing A] : ℕ := nilpotencyClass (nilradical A) + 1

theorem localExponent_pos : 0 < localExponent A := Nat.zero_lt_succ _

theorem nilradical_pow_localExponent [IsArtinianRing A] :
    nilradical A ^ localExponent A = ⊥ := by
  change nilradical A ^ (nilpotencyClass (nilradical A) + 1) = 0
  rw [pow_succ, pow_nilpotencyClass IsArtinianRing.isNilpotent_nilradical,
    zero_mul]

def LocalComponent (A : Type*) [CommRing A] (m : MaximalSpectrum A) :=
  A ⧸ m.asIdeal ^ localExponent A

instance localComponentCommRing (m : MaximalSpectrum A) : CommRing (LocalComponent A m) :=
  inferInstanceAs (CommRing (A ⧸ m.asIdeal ^ localExponent A))

instance localComponentLocal (m : MaximalSpectrum A) : IsLocalRing (LocalComponent A m) :=
  local_quotient_maximal_power m.asIdeal _ localExponent_pos

variable {F : Type*} [Field F] [Algebra F A]

instance localComponentAlgebra (m : MaximalSpectrum A) : Algebra F (LocalComponent A m) :=
  inferInstanceAs (Algebra F (A ⧸ m.asIdeal ^ localExponent A))

def localDecomposition [IsArtinianRing A] :
    A ≃ₐ[F] ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal ^ localExponent A :=
  ((AlgEquiv.quotientBot F A).symm.trans
    (Ideal.quotientEquivAlgOfEq F nilradical_pow_localExponent.symm)).trans
      ((IsArtinianRing.quotNilradicalPowEquivPi A (localExponent A)).restrictScalars F)

theorem finrank_localDecomposition [IsArtinianRing A] [Module.Finite F A]
    [Fintype (MaximalSpectrum A)] :
    Module.finrank F A =
      ∑ m : MaximalSpectrum A, Module.finrank F (A ⧸ m.asIdeal ^ localExponent A) := by
  let : ∀ m : MaximalSpectrum A, Module.Finite F (A ⧸ m.asIdeal ^ localExponent A) :=
    fun m => Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ F (m.asIdeal ^ localExponent A)).toLinearMap
      Ideal.Quotient.mk_surjective
  have h := (localDecomposition (F := F) (A := A)).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_pi_fintype] using h

section Idempotents

variable {ι : Type*} [Fintype ι] {B : ι → Type*}
  [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]

def blockIdempotent (e : A ≃ₐ[F] ∀ i, B i) (i : ι) : A := e.symm (Pi.single i 1)

omit [Fintype ι] in
@[simp] theorem blockIdempotent_image (e : A ≃ₐ[F] ∀ i, B i) (i : ι) :
    e (blockIdempotent e i) = Pi.single i 1 := e.apply_symm_apply _

omit [Fintype ι] in
theorem blockIdempotent_sq (e : A ≃ₐ[F] ∀ i, B i) (i : ι) :
    blockIdempotent e i * blockIdempotent e i = blockIdempotent e i := by
  apply e.injective
  simp only [map_mul, blockIdempotent_image]
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [Fintype ι] in
theorem blockIdempotent_mul (e : A ≃ₐ[F] ∀ i, B i) {i j : ι} (h : i ≠ j) :
    blockIdempotent e i * blockIdempotent e j = 0 := by
  apply e.injective
  simp only [map_mul, blockIdempotent_image, map_zero]
  funext k
  by_cases hi : k = i
  · subst k; simp [h]
  · simp [hi]

theorem sum_blockIdempotent (e : A ≃ₐ[F] ∀ i, B i) :
    ∑ i, blockIdempotent e i = 1 := by
  apply e.injective
  simp only [map_sum, blockIdempotent_image, map_one]
  exact Finset.univ_sum_single (fun i => (1 : B i))

end Idempotents

end Lemmata.Centroid.Linear
