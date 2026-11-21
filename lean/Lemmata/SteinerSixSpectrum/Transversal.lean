module

public import Lemmata.SteinerSixSpectrum.Assembly
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic.Ring

public section

namespace Lemmata.SteinerSixSpectrum

/-- The affine array has one column for each coefficient, with a final column for
the second coordinate itself. -/
@[expose] def affineRow {I A : Type*} [Ring A] (c : I → A) (p : A × A) :
    I ⊕ Unit → A
  | .inl i => p.1 + c i * p.2
  | .inr _ => p.2

theorem affine_transversal {I A : Type*} [CommRing A] (c : I → A)
    (unit : ∀ i j, i ≠ j → IsUnit (c j - c i)) :
    IsTransversal (affineRow c) := by
  rintro (i | ⟨⟩) (j | ⟨⟩) hn a b
  · have hij : i ≠ j := fun h => hn (congrArg Sum.inl h)
    obtain ⟨u, hu⟩ := unit i j hij
    let v : A := (↑u⁻¹ : A) * (b - a)
    have hv : (c j - c i) * v = b - a := by
      rw [← hu]
      simp [v, ← mul_assoc]
    refine ⟨(a - c i * v, v), ⟨by simp [affineRow], ?_⟩, ?_⟩
    · change a - c i * v + c j * v = b
      calc
        _ = a + (c j - c i) * v := by ring
        _ = b := by rw [hv]; ring
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      change x + c i * y = a at hx
      change x + c j * y = b at hy
      have eq : (c j - c i) * y = (c j - c i) * v := by
        calc
          _ = (x + c j * y) - (x + c i * y) := by ring
          _ = _ := by rw [hx, hy, hv]
      rw [← hu] at eq
      have hy' : y = v := by
        simpa only [← mul_assoc, Units.inv_mul, one_mul] using
          congrArg (fun z => (↑u⁻¹ : A) * z) eq
      subst y
      exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) rfl
  · refine ⟨(a - c i * b, b), ⟨by simp [affineRow], rfl⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change x + c i * y = a at hx
    change y = b at hy
    subst y
    exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) rfl
  · refine ⟨(b - c j * a, a), ⟨rfl, by simp [affineRow]⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hy, hx⟩
    change y = a at hy
    change x + c j * y = b at hx
    subst y
    exact Prod.ext ((eq_sub_iff_add_eq).mpr hx) rfl
  · exact (hn rfl).elim

/-- The modular affine array works whenever each nonzero coefficient difference
is relatively prime to the modulus. -/
theorem modular_transversal {k t : ℕ}
    (coprime : ∀ d : ℕ, 0 < d → d < k → Nat.Coprime d t) :
    IsTransversal (affineRow (fun i : Fin k => (i.val : ZMod t))) := by
  apply affine_transversal
  have asc (i j : Fin k) (h : i.val < j.val) :
      IsUnit ((j.val : ZMod t) - (i.val : ZMod t)) := by
    rw [← Nat.cast_sub (Nat.le_of_lt h), ZMod.isUnit_iff_coprime]
    exact coprime _ (by omega) (by have hj := j.isLt; omega)
  intro i j hij
  have h : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
  rcases lt_or_gt_of_ne h with h | h
  · exact asc i j h
  · simpa only [neg_sub] using (asc j i h).neg

/-- Transport the symbol type of an array along an equivalence. -/
theorem IsTransversal.relabel {I T U A : Type*} {row : A → I → T}
    (td : IsTransversal row) (e : T ≃ U) :
    IsTransversal (fun a i => e (row a i)) := by
  intro i j h x y
  obtain ⟨a, ⟨hx, hy⟩, unique⟩ := td i j h (e.symm x) (e.symm y)
  refine ⟨a, ⟨by simp [hx], by simp [hy]⟩, ?_⟩
  intro b ⟨hbx, hby⟩
  exact unique b
    ⟨e.injective (hbx.trans (e.apply_symm_apply x).symm),
      e.injective (hby.trans (e.apply_symm_apply y).symm)⟩

/-- Use an affine array over a finite field of cardinality p^m. -/
theorem field_transversal {k p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) (hk : k ≤ p^m) :
    ∃ row : (GaloisField p m × GaloisField p m) → (Fin k ⊕ Unit) → Fin (p^m),
      IsTransversal row := by
  classical
  let := Fintype.ofFinite (GaloisField p m)
  have hs : Fintype.card (GaloisField p m) = p^m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p m hm]
  let e : GaloisField p m ≃ Fin (p^m) := Fintype.equivOfCardEq (by simpa using hs)
  let c : Fin k → GaloisField p m := fun i => e.symm (Fin.castLE hk i)
  have injective : Function.Injective c := fun _ _ h =>
    Fin.ext (congrArg (fun z : Fin (p^m) => z.val) (e.symm.injective h))
  exact ⟨_, (affine_transversal c (fun i j h =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h' => h (injective h').symm)))).relabel e⟩

end Lemmata.SteinerSixSpectrum
