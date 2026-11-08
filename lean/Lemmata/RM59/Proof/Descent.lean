module

public import Lemmata.RM59.Proof.Model
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59

open scoped BigOperators CharTwo symmDiff

def translateSupport {m : ℕ} (P : Finset (Point m)) (t : Point m) : Finset (Point m) :=
  P.image fun x => x + t

private theorem supportMoment_eq_sum_ite {m : ℕ} (P : Finset (Point m))
    (s : Finset (Fin m)) :
    supportMoment P s = ∑ x, if x ∈ P then monomial s x else 0 := by
  classical
  exact (Finset.sum_ite_mem_eq P (monomial s)).symm

private theorem supportMoment_sdiff_add {m : ℕ} {P Q : Finset (Point m)}
    (hQP : Q ⊆ P) (s : Finset (Fin m)) :
    supportMoment (P \ Q) s + supportMoment Q s = supportMoment P s := by
  classical
  rw [supportMoment_eq_sum_ite, supportMoment_eq_sum_ite,
    supportMoment_eq_sum_ite, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : x ∈ Q
  · simp [hq, hQP hq]
  · by_cases hp : x ∈ P <;> simp [hp, hq]

theorem matchSupportMoments_odd {m : ℕ} {P Q : Finset (Point m)}
    (h : MatchSupportMoments 2 P Q) (hQ : Odd Q.card) : Odd P.card := by
  apply (supportMoment_empty_eq_one_iff P).mp
  rw [h ∅ (by simp)]
  exact (supportMoment_empty_eq_one_iff Q).mpr hQ

theorem translateSupport_moments_two {m : ℕ} (Q : Finset (Point m)) (t : Point m)
    (hzero : (Q.card : Field) = 0) (hfirst : ∀ i, ∑ x ∈ Q, x i = 0) :
    MatchSupportMoments 2 (translateSupport Q t) Q := by
  classical
  intro s hs
  have himage : Function.Injective (fun x : Point m => x + t) :=
    fun _ _ h => add_right_cancel h
  rw [supportMoment, translateSupport, Finset.sum_image himage.injOn]
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with h | h | h
  · have : s = ∅ := Finset.card_eq_zero.mp h
    subst s
    simp [supportMoment, monomial_eq_prod]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simp [supportMoment, monomial_eq_prod, Finset.sum_add_distrib, hfirst, hzero,
      nsmul_eq_mul]
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    simp only [supportMoment, monomial_eq_prod, Finset.prod_pair hij, Pi.add_apply]
    change (∑ x ∈ Q, (x i + t i) * (x j + t j)) = ∑ x ∈ Q, x i * x j
    calc
      (∑ x ∈ Q, (x i + t i) * (x j + t j)) =
          (∑ x ∈ Q, x i * x j) + (∑ x ∈ Q, x i) * t j +
            t i * (∑ x ∈ Q, x j) + (Q.card : Field) * (t i * t j) := by
        simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
          Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
      _ = _ := by rw [hfirst i, hfirst j, hzero]; ring

private theorem binary_dependency {m : ℕ} {P : Finset (Point m)}
    (h : ¬ AffineIndependent Field ((↑) : P → Point m)) :
    ∃ Q ⊆ P, Q.Nonempty ∧ (Q.card : Field) = 0 ∧ ∑ x ∈ Q, x = 0 := by
  classical
  obtain ⟨f, hvec, hsum, x, hx, hfx⟩ :=
    exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  let Q := P.filter fun x => f x ≠ 0
  have hone {y : Point m} (hy : f y ≠ 0) : f y = 1 :=
    (field_eq_zero_or_one (f y)).resolve_left hy
  refine ⟨Q, Finset.filter_subset _ _, ⟨x, by simp [Q, hx, hfx]⟩, ?_, ?_⟩
  · calc
      (Q.card : Field) = ∑ y ∈ Q, (1 : Field) := by simp
      _ = ∑ y ∈ P, f y := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f y = 0 <;> simp [hy, hone]
      _ = 0 := hsum
  · calc
      (∑ y ∈ Q, y) = ∑ y ∈ P, f y • y := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f y = 0 <;> simp [hy, hone]
      _ = 0 := hvec

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (P Q : Finset α) :
    (P ∆ Q).card + 2 * (P ∩ Q).card = P.card + Q.card := by
  have hd : Disjoint (P \ Q) (Q \ P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have hp := Finset.card_sdiff_add_card_inter P Q
  have hq := Finset.card_sdiff_add_card_inter Q P
  rw [Finset.inter_comm Q P] at hq
  omega

theorem shrink_dependent_odd_support {m : ℕ} {P : Finset (Point m)}
    (hodd : Odd P.card) (hdep : ¬ AffineIndependent Field ((↑) : P → Point m)) :
    ∃ P' : Finset (Point m), P'.card < P.card ∧ MatchSupportMoments 2 P' P := by
  classical
  obtain ⟨Q, hQP, hQ, hQzero, hQsum⟩ := binary_dependency hdep
  have hQne : Q ≠ P := by
    intro h
    rw [h, hodd.natCast_zmod_two] at hQzero
    exact one_ne_zero hQzero
  obtain ⟨p, hpP, hpQ⟩ : ∃ p ∈ P, p ∉ Q := by
    by_contra! h
    exact hQne (Finset.Subset.antisymm hQP h)
  obtain ⟨q, hq⟩ := hQ
  let t := p + q
  let R := P \ Q
  let G := translateSupport Q t
  have htrans : MatchSupportMoments 2 G Q := by
    apply translateSupport_moments_two Q t hQzero
    intro i
    have h := congrFun hQsum i
    simpa using h
  have hpG : p ∈ G := by
    apply Finset.mem_image.mpr
    refine ⟨q, hq, ?_⟩
    ext i
    simp [t, add_comm, add_left_comm, add_assoc]
  have hpR : p ∈ R := by simp [R, hpP, hpQ]
  have hpos : 0 < (R ∩ G).card :=
    Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpR, hpG⟩⟩
  have hGcard : G.card = Q.card :=
    Finset.card_image_of_injective Q (fun _ _ h => add_right_cancel h)
  have hRcard : R.card + Q.card = P.card :=
    Finset.card_sdiff_add_card_eq_card hQP
  refine ⟨R ∆ G, ?_, ?_⟩
  · have hc := card_symmDiff_add_twice_inter R G
    omega
  · intro s hs
    rw [supportMoment_symmDiff, htrans s hs]
    exact supportMoment_sdiff_add hQP s

theorem exists_affineIndependent_matchSupportMoments_two {m : ℕ}
    (S : Finset (Point m)) (hodd : Odd S.card) :
    ∃ P : Finset (Point m), AffineIndependent Field ((↑) : P → Point m) ∧
      Odd P.card ∧ MatchSupportMoments 2 P S ∧ P.card ≤ S.card := by
  classical
  let Good (n : ℕ) := ∃ P : Finset (Point m), P.card = n ∧ MatchSupportMoments 2 P S
  have hex : ∃ n, Good n := ⟨S.card, S, rfl, fun _ _ => rfl⟩
  obtain ⟨P, hcard, hmatch⟩ := Nat.find_spec hex
  have hmin (Q : Finset (Point m)) (hQ : MatchSupportMoments 2 Q S) :
      P.card ≤ Q.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨Q, rfl, hQ⟩
  have hPodd := matchSupportMoments_odd hmatch hodd
  have hind : AffineIndependent Field ((↑) : P → Point m) := by
    by_contra hdep
    obtain ⟨Q, hlt, hQP⟩ := shrink_dependent_odd_support hPodd hdep
    have hQS : MatchSupportMoments 2 Q S :=
      fun s hs => (hQP s hs).trans (hmatch s hs)
    have := hmin Q hQS
    omega
  exact ⟨P, hind, hPodd, hmatch, hmin S (fun _ _ => rfl)⟩

theorem affineIndependent_support_card_le {m : ℕ} (P : Finset (Point m))
    (hind : AffineIndependent Field ((↑) : P → Point m)) : P.card ≤ m + 1 := by
  classical
  calc
    P.card = Fintype.card P := (Fintype.card_coe P).symm
    _ ≤ Module.finrank Field (vectorSpan Field (Set.range ((↑) : P → Point m))) + 1 :=
      hind.card_le_finrank_succ
    _ ≤ Module.finrank Field (Point m) + 1 :=
      Nat.add_le_add_right (Submodule.finrank_le _) 1
    _ = m + 1 := by simp [Point]

theorem exists_odd_simplex_matchSupportMoments_two (S : Finset (Point 9))
    (hodd : Odd S.card) :
    ∃ P : Finset (Point 9), AffineIndependent Field ((↑) : P → Point 9) ∧
      P.card ∈ ({1, 3, 5, 7, 9} : Finset ℕ) ∧ MatchSupportMoments 2 P S := by
  obtain ⟨P, hind, hPodd, hmatch, _⟩ :=
    exists_affineIndependent_matchSupportMoments_two S hodd
  have hcard : P.card ≤ 10 := affineIndependent_support_card_le P hind
  refine ⟨P, hind, ?_, hmatch⟩
  obtain ⟨k, hk⟩ := hPodd
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end Lemmata.RM59
