module

public import Lemmata.SteinerSixSpectrum.Filling
public import Mathlib.Data.Fintype.BigOperators

public section

namespace Lemmata.SteinerSixSpectrum

abbrev Columns (k : ℕ) := Fin k ⊕ Unit

/-- The cell sizes in a row template. There are k ordinary groups of five and
one special group of size d. -/
@[expose] def RowCell {k : ℕ} (d : ℕ) : Columns k → Type
  | .inl _ => Fin 5
  | .inr _ => Fin d

abbrev RowTemplate (k d : ℕ) :=
  PairDesign (Σ i : Columns k, RowCell d i) (fun x y => x.1 ≠ y.1)

private def cell {k r s : ℕ} (light heavy : ℕ) (i : Columns k) (x : Fin r ⊕ Fin s) : Type :=
  RowCell (match x with | .inl _ => heavy | .inr _ => light) i

private instance cellFintype {k r s : ℕ} (light heavy : ℕ) (i : Columns k) (x : Fin r ⊕ Fin s) :
    Fintype (cell light heavy i x) := by
  cases i <;> cases x <;> exact inferInstanceAs (Fintype (Fin _))

private def groupSize {k : ℕ} (r s light heavy : ℕ) : Columns k → ℕ
  | .inl _ => 5*(r+s)
  | .inr _ => heavy*r+light*s

private theorem card_group {k r s : ℕ} (light heavy : ℕ) (i : Columns k) :
    Fintype.card (Σ x : Fin r ⊕ Fin s, cell light heavy i x) =
      groupSize r s light heavy i := by
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  cases i with
  | inl i =>
    have f₁ (x : Fin r) : Fintype.card (cell light heavy (.inl i) (.inl x : Fin r ⊕ Fin s)) = 5 :=
      Fintype.card_fin _
    have f₂ (x : Fin s) : Fintype.card (cell light heavy (.inl i) (.inr x : Fin r ⊕ Fin s)) = 5 :=
      Fintype.card_fin _
    simp [f₁, f₂, groupSize, Nat.mul_comm, Nat.add_mul]
  | inr u =>
    have f₁ (x : Fin r) :
        Fintype.card (cell light heavy (.inr u : Columns k) (.inl x : Fin r ⊕ Fin s)) = heavy :=
      Fintype.card_fin _
    have f₂ (x : Fin s) :
        Fintype.card (cell light heavy (.inr u : Columns k) (.inr x : Fin r ⊕ Fin s)) = light :=
      Fintype.card_fin _
    simp [f₁, f₂, groupSize, Nat.mul_comm]

/-- Apply the two row templates to the two classes of symbols in the final
column, then fill the resulting groups with shared points. -/
theorem wilsonStep {k r s light heavy e : ℕ} {A : Type}
    {rows : A → Columns k → (Fin r ⊕ Fin s)} (td : IsTransversal rows)
    (ordinary : RowTemplate k light) (special : RowTemplate k heavy)
    (shared : e = 1 ∨ e = 6)
    (large : Nonempty (SteinerSystem (Fin (5*(r+s)+e))))
    (small : Nonempty (SteinerSystem (Fin (heavy*r+light*s+e)))) :
    Nonempty (SteinerSystem (Fin (k*(5*(r+s)) + (heavy*r+light*s) + e))) := by
  classical
  let W := cell (k := k) (r := r) (s := s) light heavy
  have localDesign (a : A) :
      PairDesign (Σ i, W i (rows a i)) (fun x y => x.1 ≠ y.1) := by
    cases h : rows a (.inr ()) with
    | inl z =>
      have shape : (fun i => W i (rows a i)) = RowCell (k := k) heavy := by
        funext i
        cases i with
        | inl i => cases rows a (.inl i) <;> rfl
        | inr u => cases u; simp [W, cell, h]
      rw [shape]
      exact special
    | inr z =>
      have shape : (fun i => W i (rows a i)) = RowCell (k := k) light := by
        funext i
        cases i with
        | inl i => cases rows a (.inl i) <;> rfl
        | inr u => cases u; simp [W, cell, h]
      rw [shape]
      exact ordinary
  let outer := weight td W localDesign
  let G := fun i => Σ x : Fin r ⊕ Fin s, W i x
  let (i : Columns k) : Fintype (G i) :=
    inferInstanceAs (Fintype (Σ x : Fin r ⊕ Fin s, cell light heavy i x))
  have gcard (i : Columns k) : Fintype.card (G i) = groupSize r s light heavy i :=
    card_group light heavy i
  have fill (i : Columns k) : Nonempty (SteinerSystem (Fin (Fintype.card (G i)+e))) := by
    rw [gcard]
    cases i
    · exact large
    · exact small
  have total : Fintype.card (Fin e ⊕ (Σ i, G i)) =
      k*(5*(r+s)) + (heavy*r+light*s) + e := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    simp [gcard, Fintype.sum_sum_type, groupSize, Nat.add_comm]
  exact fillToOrder outer (Or.inr shared) fill total

end Lemmata.SteinerSixSpectrum
