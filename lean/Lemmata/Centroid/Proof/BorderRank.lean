module

public import Lemmata.Centroid.Proof.Polynomial.Budget
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

open scoped BigOperators
open Classical

namespace Lemmata.Centroid

noncomputable section

namespace RationalFunction

variable {F : Type*} [Field F]

/-- A rational function is regular at zero when its reduced denominator is nonzero there. -/
def Regular (f : RatFunc F) : Prop := f.denom.eval 0 ≠ 0

theorem regular_polynomial (p : Polynomial F) :
    Regular (algebraMap (Polynomial F) (RatFunc F) p) := by
  simp [Regular]

theorem regular_zero : Regular (0 : RatFunc F) := by simp [Regular]

theorem regular_one : Regular (1 : RatFunc F) := by simp [Regular]

theorem Regular.add {f g : RatFunc F} (hf : Regular f) (hg : Regular g) :
    Regular (f + g) := by
  intro h
  have hz := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    (RingHom.id F) 0 (RatFunc.denom_add_dvd f g) h
  simp only [Polynomial.eval₂_mul] at hz
  exact (mul_ne_zero hf hg) hz

theorem Regular.mul {f g : RatFunc F} (hf : Regular f) (hg : Regular g) :
    Regular (f * g) := by
  intro h
  have hz := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    (RingHom.id F) 0 (RatFunc.denom_mul_dvd f g) h
  simp only [Polynomial.eval₂_mul] at hz
  exact (mul_ne_zero hf hg) hz

theorem Regular.neg {f : RatFunc F} (hf : Regular f) : Regular (-f) := by
  have hn := regular_polynomial (Polynomial.C (-1 : F))
  have h := hn.mul hf
  simpa using h

def regularSubring (F : Type*) [Field F] : Subring (RatFunc F) where
  carrier := Regular
  zero_mem' := regular_zero
  one_mem' := regular_one
  add_mem' := Regular.add
  mul_mem' := Regular.mul
  neg_mem' := Regular.neg

/-- Specialization is a ring homomorphism on the functions regular at zero. -/
def specialize : regularSubring F →+* F where
  toFun f := RatFunc.eval (RingHom.id F) 0 f.val
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' f g := RatFunc.eval_add (RingHom.id F) 0 f.property g.property
  map_mul' f g := RatFunc.eval_mul (RingHom.id F) 0 f.property g.property

def ofPolynomial (p : Polynomial F) : regularSubring F :=
  ⟨algebraMap (Polynomial F) (RatFunc F) p, regular_polynomial p⟩

@[simp] theorem specialize_ofPolynomial (p : Polynomial F) :
    specialize (ofPolynomial p) = p.eval 0 := by
  simp [specialize, ofPolynomial, RatFunc.eval_algebraMap,
    Polynomial.coeff_zero_eq_eval_zero]

theorem exists_common_denominator {J : Type*} [Fintype J] (f : J → RatFunc F) :
    ∃ D : Polynomial F, D ≠ 0 ∧ ∀ j, ∃ p : Polynomial F,
      algebraMap (Polynomial F) (RatFunc F) D * f j = algebraMap _ _ p := by
  classical
  let D : Polynomial F := ∏ j, (f j).denom
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (f j).denom_ne_zero
  refine ⟨D, hD, fun j => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j => (f j).denom) (Finset.mem_univ j)
  refine ⟨q * (f j).num, ?_⟩
  rw [show D = (f j).denom * q from hq, map_mul, map_mul]
  have hn := RatFunc.algebraMap_ne_zero (f j).denom_ne_zero
  have hh := (div_eq_iff hn).mp (RatFunc.num_div_denom (f j))
  calc
    _ = algebraMap (Polynomial F) (RatFunc F) q *
        (f j * algebraMap (Polynomial F) (RatFunc F) (f j).denom) := by ring
    _ = _ := by rw [← hh]

/-- A finite polynomial family over `F(z)` can be evaluated at a rational parameter
whose positive terms are regular and vanish at zero. -/
theorem regularize_polynomial_family {J : Type*} [Fintype J]
    (P : J → Polynomial (RatFunc F)) (T : J → F)
    (hconstant : ∀ j, (P j).coeff 0 = algebraMap F (RatFunc F) (T j)) :
    ∃ e : RatFunc F, e ≠ 0 ∧ ∀ j, ∃ q : Polynomial F,
      algebraMap (Polynomial F) (RatFunc F) q = (P j).eval e ∧ q.eval 0 = T j := by
  classical
  let N := Finset.univ.sup (fun j => (P j).natDegree)
  have hN (j : J) : (P j).natDegree ≤ N :=
    Finset.le_sup (f := fun j : J => (P j).natDegree) (Finset.mem_univ j)
  obtain ⟨D, hD, hnum⟩ := exists_common_denominator
    (fun j : J × Fin (N + 1) => (P j.1).coeff j.2.val)
  let φ := algebraMap (Polynomial F) (RatFunc F)
  let e := φ Polynomial.X * φ D
  have he : e ≠ 0 := mul_ne_zero
    (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero) (RatFunc.algebraMap_ne_zero hD)
  choose p hp using hnum
  refine ⟨e, he, fun j => ?_⟩
  let q : Polynomial F := ∑ k : Fin (N + 1),
    if k.val = 0 then Polynomial.C (T j)
    else Polynomial.X ^ k.val * D ^ (k.val - 1) * p (j, k)
  refine ⟨q, ?_, ?_⟩
  · rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hN j))]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [q, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hz : k.val = 0
    · simp [hz, hconstant]
    · obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hm := hp (j, k)
      change φ D * (P j).coeff k.val = φ (p (j, k)) at hm
      simp only [ite_eq_right hz, map_mul, map_pow]
      rw [← hm, ha]
      simp only [Nat.succ_sub_one]
      dsimp [e, φ]
      ring
  · simp only [q, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1))]
    · simp
    · intro k hk hne
      have hz : k.val ≠ 0 := by
        intro hz
        exact hne (Fin.ext hz)
      simp [hz]
    · simp

end RationalFunction

namespace Tensor

universe u v w

variable {F : Type u} {ι : Type v} {V : ι → Type w}
variable [Field F] [Fintype ι]

/-- A rational CP family whose sum is regular at zero and specializes to the target. -/
structure RationalCertificate (T : Tensor F ι V) (r : ℕ) where
  family : Tensor (RatFunc F) ι V
  rank_bound : RankAtMost family r
  regular : ∀ x, RationalFunction.Regular (family x)
  value : ∀ x, RatFunc.eval (RingHom.id F) 0 (family x) = T x

def RationalBorderRankAtMost (T : Tensor F ι V) (r : ℕ) : Prop :=
  Nonempty (RationalCertificate T r)

theorem RankAtMost.rationalBorderRankAtMost {T : Tensor F ι V} {r : ℕ}
    (hT : RankAtMost T r) : RationalBorderRankAtMost T r := by
  refine ⟨⟨Tensor.mapCoefficients (algebraMap F (RatFunc F)) T,
    hT.mapCoefficients _, ?_, ?_⟩⟩
  · intro x
    simpa using RationalFunction.regular_polynomial (Polynomial.C (T x))
  · intro x
    simp [Tensor.mapCoefficients]

theorem RationalBorderRankAtMost.mono [Nonempty ι] {T : Tensor F ι V} {r s : ℕ}
    (hT : RationalBorderRankAtMost T r) (hrs : r ≤ s) :
    RationalBorderRankAtMost T s := by
  obtain ⟨A⟩ := hT
  exact ⟨{ A with rank_bound := A.rank_bound.mono hrs }⟩

theorem RationalBorderRankAtMost.add {T S : Tensor F ι V} {r s : ℕ}
    (hT : RationalBorderRankAtMost T r) (hS : RationalBorderRankAtMost S s) :
    RationalBorderRankAtMost (T + S) (r + s) := by
  obtain ⟨A⟩ := hT
  obtain ⟨B⟩ := hS
  refine ⟨⟨A.family + B.family, A.rank_bound.add B.rank_bound,
    fun x => (A.regular x).add (B.regular x), ?_⟩⟩
  intro x
  rw [Pi.add_apply, RatFunc.eval_add (RingHom.id F) 0 (A.regular x) (B.regular x),
    A.value, B.value]
  rfl

theorem RationalBorderRankAtMost.restrict {W : ι → Type*}
    {T : Tensor F ι V} {r : ℕ} (hT : RationalBorderRankAtMost T r)
    (f : ∀ i, W i → V i) : RationalBorderRankAtMost (Tensor.restrict f T) r := by
  obtain ⟨A⟩ := hT
  exact ⟨⟨Tensor.restrict f A.family, A.rank_bound.restrict f,
    fun x => A.regular _, fun x => A.value _⟩⟩

section Transport

variable {κ : Type*} {W : κ → Type*} [Fintype κ]

def transport (e : ι ≃ κ) (c : ∀ i, V i ≃ W (e i)) (T : Tensor F ι V) :
    Tensor F κ W := fun y => T ((e.piCongr c).symm y)

def transportFactors (e : ι ≃ κ) (c : ∀ i, V i ≃ W (e i))
    (u : ∀ i, V i → F) : ∀ j, W j → F :=
  e.piCongr (fun i => Equiv.arrowCongr (c i) (Equiv.refl F)) u

theorem transport_simple (e : ι ≃ κ) (c : ∀ i, V i ≃ W (e i))
    (u : ∀ i, V i → F) :
    transport e c (simple u) = simple (transportFactors e c u) := by
  funext y
  obtain ⟨x, rfl⟩ := (e.piCongr c).surjective y
  simp only [transport, Equiv.symm_apply_apply, simple, Lemmata.TensorRank.Tensor.pure]
  rw [← e.prod_comp (fun j => transportFactors e c u j (e.piCongr c x j))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [transportFactors, Equiv.piCongr_apply_apply]

theorem RankAtMost.transport {T : Tensor F ι V} {r : ℕ}
    (h : RankAtMost T r) (e : ι ≃ κ) (c : ∀ i, V i ≃ W (e i)) :
    RankAtMost (Tensor.transport e c T) r := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun q => transportFactors e c (u q), ?_⟩
  have hsum : Tensor.transport e c (∑ q, simple (u q)) =
      ∑ q, Tensor.transport e c (simple (u q)) := by
    funext y
    simp [Tensor.transport]
  rw [hsum]
  simp only [Tensor.transport_simple]

theorem RationalBorderRankAtMost.transport {T : Tensor F ι V} {r : ℕ}
    (h : RationalBorderRankAtMost T r) (e : ι ≃ κ) (c : ∀ i, V i ≃ W (e i)) :
    RationalBorderRankAtMost (Tensor.transport e c T) r := by
  obtain ⟨A⟩ := h
  refine ⟨⟨Tensor.transport e c A.family, A.rank_bound.transport e c,
    fun y => A.regular _, fun y => A.value _⟩⟩

end Transport

/-- A square minor of a single-party flattening. -/
def flatteningMinor {J : Type*} [DecidableEq ι]
    (T : Tensor F ι V) (i : ι) (row : J → V i)
    (column : J → ∀ j, V j) : Matrix J J F :=
  fun a b => T (Function.update (column b) i (row a))

theorem RankAtMost.flatteningMinor_rank_le {J : Type*} [Fintype J]
    [DecidableEq ι] {T : Tensor F ι V} {r : ℕ} (hT : RankAtMost T r)
    (i : ι) (row : J → V i) (column : J → ∀ j, V j) :
    (flatteningMinor T i row column).rank ≤ r := by
  classical
  obtain ⟨u, rfl⟩ := hT
  let A : Matrix J (Fin r) F := fun a q => u q i (row a)
  let B : Matrix (Fin r) J F := fun q b =>
    ∏ j ∈ Finset.univ.erase i, u q j (column b j)
  have hmul : flatteningMinor (∑ q, simple (u q)) i row column = A * B := by
    funext a b
    simp only [flatteningMinor, Finset.sum_apply, A, B, simple, Lemmata.TensorRank.Tensor.pure]
    apply Finset.sum_congr rfl
    intro q hq
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (u q j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _)
  rw [hmul]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width A)

theorem RationalBorderRankAtMost.card_le_of_flatteningMinor
    {J : Type*} [Fintype J] [DecidableEq J] [DecidableEq ι]
    {T : Tensor F ι V} {r : ℕ} (hT : RationalBorderRankAtMost T r)
    (i : ι) (row : J → V i) (column : J → ∀ j, V j)
    (hminor : (flatteningMinor T i row column).det ≠ 0) :
    Fintype.card J ≤ r := by
  obtain ⟨A⟩ := hT
  let M : Matrix J J (RationalFunction.regularSubring F) :=
    fun a b => ⟨A.family (Function.update (column b) i (row a)), A.regular _⟩
  have hspecialize : RationalFunction.specialize.mapMatrix M =
      flatteningMinor T i row column := by
    funext a b
    change RatFunc.eval (RingHom.id F) 0
      (A.family (Function.update (column b) i (row a))) = _
    exact A.value _
  have hdet : (flatteningMinor A.family i row column).det ≠ 0 := by
    intro hz
    have hz' : M.det = 0 := by
      apply Subtype.val_injective
      change (Subring.subtype (RationalFunction.regularSubring F)) M.det = 0
      rw [RingHom.map_det]
      exact hz
    have hh := congrArg RationalFunction.specialize hz'
    rw [RingHom.map_det, hspecialize, map_zero] at hh
    exact hminor hh
  rw [← Matrix.rank_of_det_ne_zero hdet]
  exact A.rank_bound.flatteningMinor_rank_le i row column

section FiniteCoordinates

variable [Nonempty ι] [∀ i, Fintype (V i)]

theorem exists_rationalCertificate (T : Tensor F ι V) :
    ∃ r, RationalBorderRankAtMost T r :=
  ⟨rank T, (rankAtMost_rank T).rationalBorderRankAtMost⟩

def rationalBorderRank (T : Tensor F ι V) : ℕ := Nat.find (exists_rationalCertificate T)

theorem rationalBorderRankAtMost_rank (T : Tensor F ι V) :
    RationalBorderRankAtMost T (rationalBorderRank T) :=
  Nat.find_spec (exists_rationalCertificate T)

theorem rationalBorderRank_le_iff (T : Tensor F ι V) (r : ℕ) :
    rationalBorderRank T ≤ r ↔ RationalBorderRankAtMost T r := by
  constructor
  · exact fun h => (rationalBorderRankAtMost_rank T).mono h
  · exact fun h => Nat.find_min' (exists_rationalCertificate T) h

end FiniteCoordinates

end Tensor

namespace PolynomialApproximation

variable {F ι : Type*} {V : ι → Type*} [Field F] [Fintype ι] [Nonempty ι]
variable {T : Tensor F ι V} {r d D : ℕ}

theorem rationalBorderRankAtMost (A : PolynomialApproximation T r d D) :
    Tensor.RationalBorderRankAtMost T r := by
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hx : φ Polynomial.X ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hr := (A.rank_bound.mapCoefficients φ).smul ((φ Polynomial.X ^ d)⁻¹)
  have heq : ((φ Polynomial.X ^ d)⁻¹) • Tensor.mapCoefficients φ A.polynomial =
      Tensor.mapCoefficients φ A.normalized := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Tensor.mapCoefficients, A.polynomial_eq,
      map_mul, map_pow]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hx), one_mul]
  rw [heq] at hr
  refine ⟨⟨Tensor.mapCoefficients φ A.normalized, hr,
    fun x => RationalFunction.regular_polynomial _, ?_⟩⟩
  intro x
  simpa [Tensor.mapCoefficients, φ, RatFunc.eval_algebraMap,
    ← Polynomial.coeff_zero_eq_eval_zero] using A.normalized_constant x

/-- Auxiliary rational parameters in a polynomial CP certificate can be eliminated. -/
theorem rationalBorderRankAtMost_of_ratFunc [∀ i, Fintype (V i)]
    (A : PolynomialApproximation
      (Tensor.mapCoefficients (algebraMap F (RatFunc F)) T) r d D) :
    Tensor.RationalBorderRankAtMost T r := by
  classical
  obtain ⟨e, he, hq⟩ := RationalFunction.regularize_polynomial_family A.normalized T
    (fun x => A.normalized_constant x)
  let E := Polynomial.evalRingHom e
  have hr := (A.rank_bound.mapCoefficients E).smul ((e ^ d)⁻¹)
  have heq : ((e ^ d)⁻¹) • Tensor.mapCoefficients E A.polynomial =
      Tensor.mapCoefficients E A.normalized := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Tensor.mapCoefficients, A.polynomial_eq,
      map_mul, map_pow]
    simp only [E, Polynomial.coe_evalRingHom, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d he), one_mul]
  rw [heq] at hr
  refine ⟨⟨Tensor.mapCoefficients E A.normalized, hr, ?_, ?_⟩⟩
  · intro x
    obtain ⟨q, hq, hq0⟩ := hq x
    change RationalFunction.Regular (E (A.normalized x))
    simp only [E, Polynomial.coe_evalRingHom]
    rw [← hq]
    exact RationalFunction.regular_polynomial q
  · intro x
    obtain ⟨q, hq, hq0⟩ := hq x
    change RatFunc.eval (RingHom.id F) 0 (E (A.normalized x)) = T x
    simp only [E, Polynomial.coe_evalRingHom]
    rw [← hq]
    simpa [RatFunc.eval_algebraMap, Polynomial.coeff_zero_eq_eval_zero] using hq0

end PolynomialApproximation

end

end Lemmata.Centroid
