module

public import Lemmata.CocubicCovering.Def.Field
public meta import Lemmata.CocubicCovering.Def.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering.Covering

open scoped BigOperators

abbrev ANF (m : ℕ) := Finset (Fin m) → Field
abbrev BooleanFunction (m : ℕ) := Vector m → Field
abbrev CubicCoefficients (m : ℕ) := {s : Finset (Fin m) // s.card = 3} → Field

def monomial {m : ℕ} (s : Finset (Fin m)) (x : Vector m) : Field :=
  ∏ i, if i ∈ s then x i else 1

def eval {m : ℕ} (p : ANF m) (x : Vector m) : Field :=
  ∑ s, p s * monomial s x

def DegreeLE {m : ℕ} (p : ANF m) (r : ℕ) : Prop :=
  ∀ s, r < s.card → p s = 0

def Homogeneous {m : ℕ} (p : ANF m) (r : ℕ) : Prop :=
  ∀ s, s.card ≠ r → p s = 0

def mulANF {m : ℕ} (p q : ANF m) : ANF m :=
  fun u => ∑ s, ∑ t, if s ∪ t = u then p s * q t else 0

theorem field_mul_self (a : Field) : a * a = a := by
  simpa only [pow_two] using ZMod.pow_card a

theorem monomial_union {m : ℕ} (s t : Finset (Fin m)) (x : Vector m) :
    monomial (s ∪ t) x = monomial s x * monomial t x := by
  unfold monomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [hs, ht, field_mul_self]

theorem eval_mulANF {m : ℕ} (p q : ANF m) : eval (mulANF p q) = eval p * eval q := by
  classical
  funext x
  calc
    eval (mulANF p q) x =
        ∑ u, ∑ s, ∑ t, (if s ∪ t = u then p s * q t else 0) * monomial u x := by
      simp only [eval, mulANF, Finset.sum_mul]
    _ = ∑ s, ∑ t, ∑ u, (if s ∪ t = u then p s * q t else 0) * monomial u x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ t, p s * q t * monomial (s ∪ t) x := by simp [ite_mul]
    _ = ∑ s, (p s * monomial s x) * (∑ t, q t * monomial t x) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [monomial_union]
      ring
    _ = eval p x * eval q x := by rw [eval, eval, Finset.sum_mul]

theorem degreeLE_mulANF {m r s : ℕ} {p q : ANF m}
    (hp : DegreeLE p r) (hq : DegreeLE q s) : DegreeLE (mulANF p q) (r + s) := by
  intro u hu
  unfold mulANF
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hab : a ∪ b = u
  · subst u
    by_cases har : r < a.card
    · simp [hp a har]
    · have hbs : s < b.card := by
        have hc := Finset.card_union_le a b
        omega
      simp [hq b hbs]
  · simp [hab]

def degreeSpace (m r : ℕ) : Submodule Field (ANF m) where
  carrier := {p | DegreeLE p r}
  zero_mem' := by intro s hs; rfl
  add_mem' := by
    intro p q hp hq s hs
    simp [hp s hs, hq s hs]
  smul_mem' := by
    intro a p hp s hs
    simp [hp s hs]

def evalLinear (m : ℕ) : ANF m →ₗ[Field] BooleanFunction m where
  toFun := eval
  map_add' p q := by
    funext x
    simp [eval, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    funext x
    simp [eval, mul_assoc, Finset.mul_sum]

def reedMuller (m r : ℕ) : Submodule Field (BooleanFunction m) :=
  (degreeSpace m r).map (evalLinear m)

theorem mem_reedMuller_iff {m r : ℕ} {f : BooleanFunction m} :
    f ∈ reedMuller m r ↔ ∃ p : ANF m, DegreeLE p r ∧ eval p = f := Iff.rfl

theorem homogeneous_degreeLE {m r : ℕ} {p : ANF m} (hp : Homogeneous p r) :
    DegreeLE p r := by
  intro s hs
  exact hp s (by omega)

theorem reedMuller_mono {m r s : ℕ} (hrs : r ≤ s) :
    reedMuller m r ≤ reedMuller m s := by
  intro f hf
  rcases mem_reedMuller_iff.mp hf with ⟨p, hp, rfl⟩
  apply mem_reedMuller_iff.mpr
  exact ⟨p, fun t ht => hp t (hrs.trans_lt ht), rfl⟩

theorem reedMuller_mul {m r s : ℕ} {f g : BooleanFunction m}
    (hf : f ∈ reedMuller m r) (hg : g ∈ reedMuller m s) :
    f * g ∈ reedMuller m (r + s) := by
  rcases mem_reedMuller_iff.mp hf with ⟨p, hp, rfl⟩
  rcases mem_reedMuller_iff.mp hg with ⟨q, hq, rfl⟩
  exact mem_reedMuller_iff.mpr ⟨mulANF p q, degreeLE_mulANF hp hq, eval_mulANF p q⟩

/-- The coefficient at a set is the cubic coefficient indexed by its complement. -/
def cubicComplement {m : ℕ} (c : CubicCoefficients m) : ANF m :=
  fun s => if h : sᶜ.card = 3 then c ⟨sᶜ, h⟩ else 0

theorem cubicComplement_homogeneous {m : ℕ} (c : CubicCoefficients m) :
    Homogeneous (cubicComplement c) (m - 3) := by
  intro s hs
  unfold cubicComplement
  split_ifs with h
  · have hc := Finset.card_compl_add_card s
    simp only [Fintype.card_fin, h] at hc
    omega
  · rfl

theorem cubicComplement_mem {m : ℕ} (c : CubicCoefficients m) :
    eval (cubicComplement c) ∈ reedMuller m (m - 3) :=
  mem_reedMuller_iff.mpr
    ⟨cubicComplement c, homogeneous_degreeLE (cubicComplement_homogeneous c), rfl⟩

private theorem sum_field : (∑ a : Field, a) = 1 := by decide
private theorem sum_one_field : (∑ _a : Field, (1 : Field)) = 0 := by decide

theorem sum_monomial {m : ℕ} (s : Finset (Fin m)) :
    (∑ x : Vector m, monomial s x) = if s = Finset.univ then 1 else 0 := by
  classical
  unfold monomial
  rw [← Fintype.prod_sum (fun (i : Fin m) (a : Field) => if i ∈ s then a else 1)]
  by_cases hs : s = Finset.univ
  · subst s
    simp [sum_field]
  · have hi : ∃ i : Fin m, i ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨i, hi⟩ := hi
    rw [if_neg hs]
    apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
    simpa only [if_neg hi] using sum_one_field

theorem sum_eval {m : ℕ} (p : ANF m) :
    (∑ x : Vector m, eval p x) = p Finset.univ := by
  classical
  unfold eval
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_monomial]
  simp

theorem sum_eval_eq_zero {m r : ℕ} {p : ANF m} (hp : DegreeLE p r) (hr : r < m) :
    (∑ x : Vector m, eval p x) = 0 := by
  rw [sum_eval]
  exact hp _ (by simpa using hr)

theorem sum_reedMuller_eq_zero {m r : ℕ} {f : BooleanFunction m}
    (hf : f ∈ reedMuller m r) (hr : r < m) : (∑ x : Vector m, f x) = 0 := by
  rcases mem_reedMuller_iff.mp hf with ⟨p, hp, rfl⟩
  exact sum_eval_eq_zero hp hr

theorem sum_mul_reedMuller_eq_zero {m r s : ℕ} {f g : BooleanFunction m}
    (hf : f ∈ reedMuller m r) (hg : g ∈ reedMuller m s) (hrs : r + s < m) :
    (∑ x : Vector m, f x * g x) = 0 :=
  sum_reedMuller_eq_zero (reedMuller_mul hf hg) hrs

def support {m : ℕ} (f : BooleanFunction m) : Finset (Vector m) :=
  Finset.univ.filter fun x => f x ≠ 0

def weight {m : ℕ} (f : BooleanFunction m) : ℕ := (support f).card

abbrev Support {m : ℕ} (f : BooleanFunction m) := {x : Vector m // f x ≠ 0}

theorem card_support {m : ℕ} (f : BooleanFunction m) :
    Fintype.card (Support f) = weight f := by
  simpa only [Support, weight, support] using Fintype.card_subtype (fun x => f x ≠ 0)

theorem support_value {m : ℕ} {f : BooleanFunction m} (x : Support f) : f x = 1 :=
  (eq_zero_or_one_of_sq_eq_self (ZMod.pow_card (f x))).resolve_left x.property

theorem sum_support {m : ℕ} (f g : BooleanFunction m) :
    (∑ x : Support g, f x) = ∑ x : Vector m, f x * g x := by
  classical
  rw [← Finset.sum_subtype (support g) (by simp [support]) f]
  simp only [support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hg : g x = 0
  · simp [hg]
  · have h1 := support_value (f := g) ⟨x, hg⟩
    simp [h1]

theorem support_gram_top_coefficient {m : ℕ} (p q g : ANF m) :
    (∑ x : Support (eval g), eval p x * eval q x) =
      mulANF (mulANF p q) g Finset.univ := by
  change (∑ x : Support (eval g), (eval p * eval q) x) = _
  rw [sum_support]
  simpa only [eval_mulANF, Pi.mul_apply] using sum_eval (mulANF (mulANF p q) g)

theorem top_mul_eq_zero {m r s : ℕ} {p q : ANF m}
    (hp : DegreeLE p r) (hq : DegreeLE q s) (hrs : r + s < m) :
    mulANF p q Finset.univ = 0 :=
  degreeLE_mulANF hp hq _ (by simpa using hrs)

def distance {m : ℕ} (f g : BooleanFunction m) : ℕ := weight (f - g)

noncomputable def cosetMinimum {m : ℕ} (r : ℕ) (f : BooleanFunction m) : ℕ := by
  classical
  exact Finset.univ.inf' (by
    exact ⟨⟨0, (reedMuller m r).zero_mem⟩, Finset.mem_univ _⟩)
    (fun p : reedMuller m r => weight (f + p.val))

noncomputable def coveringRadius (m r s : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup fun f : reedMuller m s => cosetMinimum r f.val

theorem le_cosetMinimum_iff {m r k : ℕ} {f : BooleanFunction m} :
    k ≤ cosetMinimum r f ↔ ∀ p ∈ reedMuller m r, k ≤ weight (f + p) := by
  classical
  constructor
  · intro h p hp
    have hmin : cosetMinimum r f ≤ weight (f + p) := by
      unfold cosetMinimum
      exact Finset.inf'_le (fun q : reedMuller m r => weight (f + q.val))
        (Finset.mem_univ (⟨p, hp⟩ : reedMuller m r))
    exact h.trans hmin
  · intro h
    unfold cosetMinimum
    exact Finset.le_inf' _ _ (fun p _ => h p.val p.property)

theorem cosetMinimum_le_weight {m r : ℕ} (f : BooleanFunction m)
    {p : BooleanFunction m} (hp : p ∈ reedMuller m r) :
    cosetMinimum r f ≤ weight (f + p) :=
  le_cosetMinimum_iff.mp le_rfl p hp

theorem cosetMinimum_le_distance {m r : ℕ} (f : BooleanFunction m)
    {p : BooleanFunction m} (hp : p ∈ reedMuller m r) :
    cosetMinimum r f ≤ distance f p := by
  simpa only [distance, sub_eq_add_neg] using
    cosetMinimum_le_weight f ((reedMuller m r).neg_mem hp)

theorem le_cosetMinimum_iff_distance {m r k : ℕ} {f : BooleanFunction m} :
    k ≤ cosetMinimum r f ↔ ∀ p ∈ reedMuller m r, k ≤ distance f p := by
  constructor
  · intro h p hp
    simpa only [distance, sub_eq_add_neg] using
      (le_cosetMinimum_iff.mp h) (-p) ((reedMuller m r).neg_mem hp)
  · intro h
    apply le_cosetMinimum_iff.mpr
    intro p hp
    simpa only [distance, sub_neg_eq_add] using h (-p) ((reedMuller m r).neg_mem hp)

set_option maxHeartbeats 1000000 in
theorem cosetMinimum_le_coveringRadius {m r s : ℕ} {f : BooleanFunction m}
    (hf : f ∈ reedMuller m s) : cosetMinimum r f ≤ coveringRadius m r s := by
  classical
  unfold coveringRadius
  exact Finset.le_sup
    (s := (Finset.univ : Finset (reedMuller m s)))
    (b := (⟨f, hf⟩ : reedMuller m s))
    (f := fun g : reedMuller m s => cosetMinimum r g.val)
    (Finset.mem_univ _)

theorem coveringRadius_lower_bound {m r s k : ℕ} {f : BooleanFunction m}
    (hf : f ∈ reedMuller m s)
    (h : ∀ p ∈ reedMuller m r, k ≤ weight (f + p)) :
    k ≤ coveringRadius m r s :=
  (le_cosetMinimum_iff.mpr h).trans (cosetMinimum_le_coveringRadius hf)

end Lemmata.CocubicCovering.Covering
