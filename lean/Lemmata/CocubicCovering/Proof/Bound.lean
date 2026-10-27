module

public import Lemmata.CocubicCovering.Proof.Model
public meta import Lemmata.CocubicCovering.Proof.Model
public import Lemmata.CocubicCovering.Proof.Linear
public meta import Lemmata.CocubicCovering.Proof.Linear

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

def restrictSupport {m : ℕ} (g : BooleanFunction m) :
    BooleanFunction m →ₗ[Field] (Support g → Field) where
  toFun f x := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def affineOnSupport {m : ℕ} (g : BooleanFunction m) :
    Submodule Field (Support g → Field) :=
  (reedMuller m 1).map (restrictSupport g)

variable {Q : Type*} [AddCommGroup Q] [Module Field Q]

def supportGram {m : ℕ} (g : BooleanFunction m)
    (e : Q →ₗ[Field] BooleanFunction m) : BilinForm Field Q :=
  gram (dotProductBilin Field Field) ((restrictSupport g).comp e)

theorem supportGram_apply {m : ℕ} (g : BooleanFunction m)
    (e : Q →ₗ[Field] BooleanFunction m) (q q' : Q) :
    supportGram g e q q' = ∑ x : Vector m, e q x * e q' x * g x := by
  change (∑ x : Support g, (e q * e q') x) = _
  exact sum_support (e q * e q') g

theorem affineOnSupport_selfOrthogonal {m : ℕ} (hm : 3 ≤ m)
    {g : BooleanFunction m} (hg : g ∈ reedMuller m (m - 3)) :
    ∀ v ∈ affineOnSupport g, ∀ w ∈ affineOnSupport g,
      ∑ x, v x * w x = 0 := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  change (∑ x : Support g, (a * b) x) = 0
  rw [sum_support]
  exact sum_mul_reedMuller_eq_zero (reedMuller_mul ha hb) hg (by omega)

/-- Evaluation on the support turns the cocubic weight bound into a Gram-rank bound. -/
theorem weight_bound_of_products {m : ℕ} (hm : 3 ≤ m)
    {g : BooleanFunction m} (hg : g ∈ reedMuller m (m - 3))
    (e : Q →ₗ[Field] BooleanFunction m)
    (he : ∀ q, e q * g ∈ reedMuller m (m - 2)) :
    2 * finrank Field (affineOnSupport g) +
      finrank Field (LinearMap.range (supportGram g e)) ≤ weight g := by
  rw [← card_support g]
  apply twice_finrank_add_gram_rank_le_card (affineOnSupport g) ((restrictSupport g).comp e)
  · exact affineOnSupport_selfOrthogonal hm hg
  · rintro _ ⟨a, ha, rfl⟩ q
    change (∑ x : Support g, (a * e q) x) = 0
    rw [sum_support]
    have hz := sum_mul_reedMuller_eq_zero ha (he q) (by omega)
    simpa only [Pi.mul_apply, mul_assoc] using hz

theorem quadratic_correction_products {m : ℕ} (hm : 4 ≤ m)
    (f h : BooleanFunction m) (hh : h ∈ reedMuller m (m - 4))
    (e : Q →ₗ[Field] BooleanFunction m)
    (he : ∀ q, e q ∈ reedMuller m 2)
    (hef : ∀ q, e q * f ∈ reedMuller m (m - 2)) :
    ∀ q, e q * (f + h) ∈ reedMuller m (m - 2) := by
  intro q
  have heh : e q * h ∈ reedMuller m (m - 2) :=
    reedMuller_mono (by omega : 2 + (m - 4) ≤ m - 2) (reedMuller_mul (he q) hh)
  simpa only [mul_add] using (reedMuller m (m - 2)).add_mem (hef q) heh

theorem weight_bound_of_correction {m : ℕ} (hm : 4 ≤ m)
    (f h : BooleanFunction m) (hf : f ∈ reedMuller m (m - 3))
    (hh : h ∈ reedMuller m (m - 4))
    (e : Q →ₗ[Field] BooleanFunction m)
    (he : ∀ q, e q ∈ reedMuller m 2)
    (hef : ∀ q, e q * f ∈ reedMuller m (m - 2)) :
    2 * finrank Field (affineOnSupport (f + h)) +
      finrank Field (LinearMap.range (supportGram (f + h) e)) ≤ weight (f + h) := by
  apply weight_bound_of_products (by omega)
    ((reedMuller m (m - 3)).add_mem hf (reedMuller_mono (by omega) hh))
  exact quadratic_correction_products hm f h hh e he hef

/-- Terms of degree at most m - 5 do not change the quadratic Gram pairing. -/
theorem supportGram_add_lowDegree {m : ℕ} (hm : 5 ≤ m)
    (g ell : BooleanFunction m) (hell : ell ∈ reedMuller m (m - 5))
    (e : Q →ₗ[Field] BooleanFunction m)
    (he : ∀ q, e q ∈ reedMuller m 2) :
    supportGram (g + ell) e = supportGram g e := by
  ext q q'
  rw [supportGram_apply, supportGram_apply]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]
  have hz : (∑ x : Vector m, e q x * e q' x * ell x) = 0 :=
    sum_mul_reedMuller_eq_zero (reedMuller_mul (he q) (he q')) hell (by omega)
  rw [hz, add_zero]

/-- Polynomials of degree at most two whose product with f has degree at most m - 2. -/
def admissibleQuadratics {m : ℕ} (f : BooleanFunction m) :
    Submodule Field (BooleanFunction m) :=
  reedMuller m 2 ⊓ (reedMuller m (m - 2)).comap (LinearMap.mulRight Field f)

theorem admissibleQuadratics_weight_bound {m : ℕ} (hm : 4 ≤ m)
    (f h : BooleanFunction m) (hf : f ∈ reedMuller m (m - 3))
    (hh : h ∈ reedMuller m (m - 4)) :
    2 * finrank Field (affineOnSupport (f + h)) +
      finrank Field (LinearMap.range
        (supportGram (f + h) (admissibleQuadratics f).subtype)) ≤ weight (f + h) := by
  apply weight_bound_of_correction hm f h hf hh
  · intro q
    exact q.property.1
  · intro q
    exact q.property.2

theorem supportGram_isSymm {m : ℕ} (g : BooleanFunction m)
    (e : Q →ₗ[Field] BooleanFunction m) : (supportGram g e).IsSymm := by
  constructor
  intro q q'
  rw [supportGram_apply, supportGram_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_comm (e q x) (e q' x)]

theorem supportGram_isAlt {m : ℕ} (hm : 3 ≤ m)
    {g : BooleanFunction m} (hg : g ∈ reedMuller m (m - 3))
    (e : Q →ₗ[Field] BooleanFunction m) (he : ∀ q, e q ∈ reedMuller m 2) :
    (supportGram g e).IsAlt := by
  intro q
  rw [supportGram_apply]
  simp_rw [field_mul_self]
  exact sum_mul_reedMuller_eq_zero (he q) hg (by omega)

end Lemmata.CocubicCovering.Covering
