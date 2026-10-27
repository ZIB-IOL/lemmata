module

public import Lemmata.CocubicCovering.Proof.Definitions
public meta import Lemmata.CocubicCovering.Proof.Definitions
public import Lemmata.CocubicCovering.Proof.Forms
public meta import Lemmata.CocubicCovering.Proof.Forms
public import Lemmata.CocubicCovering.Proof.Geometry
public meta import Lemmata.CocubicCovering.Proof.Geometry
public import Lemmata.CocubicCovering.Proof.Pairing
public meta import Lemmata.CocubicCovering.Proof.Pairing

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

theorem homogeneousQuadratics_le_reedMuller (m : ℕ) :
    homogeneousQuadratics m ≤ reedMuller m 2 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact monomial_mem_reedMuller s.val s.property.le

@[simp] theorem pairing_apply {m : ℕ} (f h : BooleanFunction m)
    (q q' : quadraticMultipliers f) :
    pairing f h q q' = ∑ x : Vector m, q.val x * q'.val x * (f + h) x := rfl

theorem pairing_eq_supportGram {m : ℕ} (f h : BooleanFunction m) :
    pairing f h = supportGram (f + h) (quadraticMultipliers f).subtype := by
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro q'
  exact (supportGram_apply (f + h) (quadraticMultipliers f).subtype q q').symm

theorem weight_bound_of_pairing {m : ℕ} (hm : 4 ≤ m) (f h : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3)) (hh : h ∈ reedMuller m (m - 4)) :
    2 * finrank Field (affineOnSupport (f + h)) + rank (pairing f h) ≤ weight (f + h) := by
  rw [pairing_eq_supportGram]
  apply weight_bound_of_correction hm f h hf hh
  · intro q
    exact homogeneousQuadratics_le_reedMuller m q.property.1
  · intro q
    exact q.property.2

theorem pairing_add_lowDegree {m : ℕ} (hm : 5 ≤ m) (f h ell : BooleanFunction m)
    (hell : ell ∈ reedMuller m (m - 5)) : pairing f (h + ell) = pairing f h := by
  rw [pairing_eq_supportGram, pairing_eq_supportGram]
  simpa only [add_assoc] using supportGram_add_lowDegree hm (f + h) ell hell
    (quadraticMultipliers f).subtype
    (fun q => homogeneousQuadratics_le_reedMuller m q.property.1)

theorem pairing_isAlt {m : ℕ} (hm : 3 ≤ m) (f h : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3)) (hh : h ∈ reedMuller m (m - 4)) :
    (pairing f h).IsAlt := by
  rw [pairing_eq_supportGram]
  exact supportGram_isAlt hm
    ((reedMuller m (m - 3)).add_mem hf (reedMuller_mono (by omega) hh))
    (quadraticMultipliers f).subtype
    (fun q => homogeneousQuadratics_le_reedMuller m q.property.1)

variable {Q : Type*} [AddCommGroup Q] [Module Field Q] [FiniteDimensional Field Q]

theorem rank_gram_pairing_le {m : ℕ} (f h : BooleanFunction m)
    (e : Q →ₗ[Field] quadraticMultipliers f) :
    rank (gram (pairing f h) e) ≤ rank (pairing f h) :=
  CoveringGeometry.gram_rank_le (pairing f h) e

theorem rank_supportGram_le_pairing {m : ℕ} (f h : BooleanFunction m)
    (e : Q →ₗ[Field] BooleanFunction m) (he : ∀ q, e q ∈ quadraticMultipliers f) :
    rank (supportGram (f + h) e) ≤ rank (pairing f h) := by
  let eQ := e.codRestrict (quadraticMultipliers f) he
  have hgram : gram (pairing f h) eQ = supportGram (f + h) e := by
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro q'
    change (∑ x : Vector m, e q x * e q' x * (f + h) x) = _
    exact (supportGram_apply (f + h) e q q').symm
  rw [← hgram]
  exact rank_gram_pairing_le f h eQ

theorem decode_mem_homogeneousQuadratics (m : ℕ) :
    ∀ polynomial : CoveringCertificate.Polynomial,
      CoveringPolynomial.Bounded m polynomial →
      (∀ term ∈ polynomial, term.card = 2) →
      eval (CoveringPolynomial.decode m polynomial) ∈ homogeneousQuadratics m := by
  intro polynomial
  induction polynomial with
  | nil =>
      intro _ _
      have hzero : eval (0 : ANF m) = (0 : BooleanFunction m) := (evalLinear m).map_zero
      simpa only [CoveringPolynomial.decode, hzero] using (homogeneousQuadratics m).zero_mem
  | cons first rest ih =>
      intro hbounded hpure
      have hfirst : (CoveringPolynomial.finiteMonomial m first).card = 2 :=
        (CoveringPairing.finiteMonomial_card first (hbounded first (by simp))).trans
          (hpure first (by simp))
      have hmonomial : monomial (CoveringPolynomial.finiteMonomial m first) ∈
          homogeneousQuadratics m :=
        Submodule.subset_span ⟨⟨CoveringPolynomial.finiteMonomial m first, hfirst⟩, rfl⟩
      have hrest := ih (fun term hterm => hbounded term (by simp [hterm]))
        (fun term hterm => hpure term (by simp [hterm]))
      have he : eval (CoveringPolynomial.decode m (first :: rest)) =
          monomial (CoveringPolynomial.finiteMonomial m first) +
            eval (CoveringPolynomial.decode m rest) := by
        funext x
        change eval (Pi.single (CoveringPolynomial.finiteMonomial m first) 1 +
          CoveringPolynomial.decode m rest) x = _
        rw [CoveringPolynomial.eval_anf_add, CoveringPolynomial.eval_single]
        rfl
      rw [he]
      exact (homogeneousQuadratics m).add_mem hmonomial hrest

end Lemmata.CocubicCovering.Covering
