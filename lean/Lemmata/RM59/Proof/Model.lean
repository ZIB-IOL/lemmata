module

public import Lemmata.CocubicCovering.Proof.Model
public meta import Lemmata.CocubicCovering.Proof.Model
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.CharP.Two

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators symmDiff

abbrev Field := Lemmata.CocubicCovering.Field
abbrev Point (m : ℕ) := Lemmata.CocubicCovering.Vector m
abbrev BooleanFunction (m : ℕ) := Lemmata.CocubicCovering.Covering.BooleanFunction m
abbrev ANF (m : ℕ) := Lemmata.CocubicCovering.Covering.ANF m
abbrev monomial {m : ℕ} := @Lemmata.CocubicCovering.Covering.monomial m
abbrev evaluate {m : ℕ} := @Lemmata.CocubicCovering.Covering.eval m
abbrev DegreeLE {m : ℕ} := @Lemmata.CocubicCovering.Covering.DegreeLE m
abbrev reedMuller := Lemmata.CocubicCovering.Covering.reedMuller

theorem monomial_eq_prod {m : ℕ} (s : Finset (Fin m)) (x : Point m) :
    monomial s x = ∏ i ∈ s, x i := by
  classical
  exact Finset.prod_ite_mem_eq s x

theorem evaluate_eq_sum {m : ℕ} (p : ANF m) (x : Point m) :
    evaluate p x = ∑ s, p s * monomial s x := rfl

def moment {m : ℕ} (f : BooleanFunction m) (s : Finset (Fin m)) : Field :=
  ∑ x, f x * monomial s x

def supportMoment {m : ℕ} (P : Finset (Point m)) (s : Finset (Fin m)) : Field :=
  ∑ x ∈ P, monomial s x

def MatchSupportMoments {m : ℕ} (d : ℕ) (P Q : Finset (Point m)) : Prop :=
  ∀ s, s.card ≤ d → supportMoment P s = supportMoment Q s

def indicator {m : ℕ} (P : Finset (Point m)) : BooleanFunction m :=
  fun x => if x ∈ P then 1 else 0

abbrev support {m : ℕ} := @Lemmata.CocubicCovering.Covering.support m
abbrev weight {m : ℕ} := @Lemmata.CocubicCovering.Covering.weight m

theorem field_mul_self (a : Field) : a * a = a := by
  simpa only [pow_two] using ZMod.pow_card a

theorem field_eq_zero_or_one (a : Field) : a = 0 ∨ a = 1 :=
  eq_zero_or_one_of_sq_eq_self (by simpa only [pow_two] using field_mul_self a)

@[simp] theorem field_add_self (a : Field) : a + a = 0 :=
  CharTwo.add_self_eq_zero a

@[simp] theorem monomial_empty {m : ℕ} (x : Point m) : monomial ∅ x = 1 := by
  simp [monomial_eq_prod]

@[simp] theorem monomial_singleton {m : ℕ} (i : Fin m) (x : Point m) :
    monomial {i} x = x i := by
  simp [monomial_eq_prod]

@[simp] theorem moment_zero {m : ℕ} (s : Finset (Fin m)) :
    moment (0 : BooleanFunction m) s = 0 := by
  simp [moment]

theorem moment_add {m : ℕ} (f g : BooleanFunction m) (s : Finset (Fin m)) :
    moment (f + g) s = moment f s + moment g s := by
  simp [moment, add_mul, Finset.sum_add_distrib]

@[simp] theorem mem_support {m : ℕ} (f : BooleanFunction m) (x : Point m) :
    x ∈ support f ↔ f x ≠ 0 := by
  simp [support, Lemmata.CocubicCovering.Covering.support]

@[simp] theorem indicator_support {m : ℕ} (f : BooleanFunction m) :
    indicator (support f) = f := by
  classical
  funext x
  rcases field_eq_zero_or_one (f x) with h | h <;> simp [indicator, h]

@[simp] theorem support_indicator {m : ℕ} (P : Finset (Point m)) :
    support (indicator P) = P := by
  classical
  ext x
  simp [indicator]

@[simp] theorem weight_indicator {m : ℕ} (P : Finset (Point m)) :
    weight (indicator P) = P.card := by
  change (support (indicator P)).card = P.card
  rw [support_indicator]

theorem indicator_symmDiff {m : ℕ} (P Q : Finset (Point m)) :
    indicator (P ∆ Q) = indicator P + indicator Q := by
  classical
  funext x
  by_cases hP : x ∈ P <;> by_cases hQ : x ∈ Q <;>
    simp [indicator, Finset.mem_symmDiff, hP, hQ]

@[simp] theorem moment_indicator {m : ℕ} (P : Finset (Point m))
    (s : Finset (Fin m)) : moment (indicator P) s = supportMoment P s := by
  classical
  unfold moment indicator supportMoment
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem moment_eq_supportMoment {m : ℕ} (f : BooleanFunction m)
    (s : Finset (Fin m)) : moment f s = supportMoment (support f) s := by
  rw [← moment_indicator, indicator_support]

theorem supportMoment_symmDiff {m : ℕ} (P Q : Finset (Point m))
    (s : Finset (Fin m)) :
    supportMoment (P ∆ Q) s = supportMoment P s + supportMoment Q s := by
  rw [← moment_indicator, indicator_symmDiff, moment_add, moment_indicator,
    moment_indicator]

@[simp] theorem supportMoment_empty {m : ℕ} (s : Finset (Fin m)) :
    supportMoment (∅ : Finset (Point m)) s = 0 := by
  simp [supportMoment]

@[simp] theorem supportMoment_singleton {m : ℕ} (x : Point m)
    (s : Finset (Fin m)) : supportMoment {x} s = monomial s x := by
  simp [supportMoment]

@[simp] theorem supportMoment_empty_index {m : ℕ} (P : Finset (Point m)) :
    supportMoment P ∅ = (P.card : Field) := by
  simp [supportMoment]

theorem supportMoment_empty_eq_one_iff {m : ℕ} (P : Finset (Point m)) :
    supportMoment P ∅ = 1 ↔ Odd P.card := by
  rw [supportMoment_empty_index, ZMod.natCast_eq_one_iff_odd]

theorem MatchSupportMoments.refl {m : ℕ} (d : ℕ) (P : Finset (Point m)) :
    MatchSupportMoments d P P := fun _ _ => rfl

theorem MatchSupportMoments.symm {m d : ℕ} {P Q : Finset (Point m)}
    (h : MatchSupportMoments d P Q) : MatchSupportMoments d Q P :=
  fun s hs => (h s hs).symm

theorem MatchSupportMoments.trans {m d : ℕ} {P Q R : Finset (Point m)}
    (hPQ : MatchSupportMoments d P Q) (hQR : MatchSupportMoments d Q R) :
    MatchSupportMoments d P R := fun s hs => (hPQ s hs).trans (hQR s hs)

theorem MatchSupportMoments.sum_evaluate {m d : ℕ} {P Q : Finset (Point m)}
    (h : MatchSupportMoments d P Q) (q : ANF m) (hq : DegreeLE q d) :
    (∑ x ∈ P, evaluate q x) = ∑ x ∈ Q, evaluate q x := by
  classical
  have expand (R : Finset (Point m)) :
      (∑ x ∈ R, evaluate q x) = ∑ s, q s * supportMoment R s := by
    simp only [evaluate_eq_sum, supportMoment]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
  rw [expand P, expand Q]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hd : s.card ≤ d
  · rw [h s hd]
  · rw [hq s (Nat.lt_of_not_ge hd), zero_mul, zero_mul]

end Lemmata.RM59
