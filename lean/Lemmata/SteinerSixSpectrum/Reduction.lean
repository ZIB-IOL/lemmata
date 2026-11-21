module

public import Lemmata.SteinerSixSpectrum.UpperOrders
public import Lemmata.SteinerSixSpectrum.Product
public import Lemmata.SteinerSixSpectrum.Templates
public meta import Lemmata.SteinerSixSpectrum.UpperOrders

public section

namespace Lemmata.SteinerSixSpectrum

@[expose] def columns (wide : Bool) : ℕ := if wide then 17 else 13

@[expose] def modulusProduct (wide : Bool) : ℕ := if wide then 30030 else 2310

@[expose] def availableArray (wide : Bool) (t : ℕ) : Prop :=
  columns wide ≤ t ∧ (t = 25 ∨ t = 27 ∨ t = 49 ∨ t = 81 ∨ t.Coprime (modulusProduct wide))

instance (wide : Bool) (t : ℕ) : Decidable (availableArray wide t) := by
  unfold availableArray
  infer_instance

private theorem differencesDvd (wide : Bool) {d : ℕ} (hd : 0 < d) (hk : d < columns wide) :
    d ∣ (modulusProduct wide)^4 := by
  cases wide
  · have table : ∀ i : Fin 13, i.val ≠ 0 → i.val ∣ (2310 : ℕ)^4 := by decide
    exact table ⟨d, hk⟩ (Nat.ne_of_gt hd)
  · have table : ∀ i : Fin 17, i.val ≠ 0 → i.val ∣ (30030 : ℕ)^4 := by decide
    exact table ⟨d, hk⟩ (Nat.ne_of_gt hd)

private theorem availableTransversal {wide : Bool} {t : ℕ} (h : availableArray wide t) :
    ∃ A : Type, ∃ row : A → Columns (columns wide) → Fin t, IsTransversal row := by
  have ⟨bound, choices⟩ := h
  rcases choices with rfl | rfl | rfl | rfl | cop
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact ⟨_, field_transversal (p := 5) (m := 2) (by decide) bound⟩
  · have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact ⟨_, field_transversal (p := 3) (m := 3) (by decide) bound⟩
  · have : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact ⟨_, field_transversal (p := 7) (m := 2) (by decide) bound⟩
  · have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact ⟨_, field_transversal (p := 3) (m := 4) (by decide) bound⟩
  · have pos : 0 < t := by cases wide <;> simp [columns] at bound <;> omega
    have : NeZero t := ⟨Nat.ne_of_gt pos⟩
    have td := modular_transversal (k := columns wide) (t := t) (fun d hz hlt =>
      ((cop.pow_right 4).of_dvd_right (differencesDvd wide hz hlt)).symm)
    exact ⟨_, _, td.relabel (ZMod.finEquiv t).toEquiv.symm⟩

structure StepParameters where
  wide : Bool
  t : ℕ
  r : ℕ
  e : ℕ

namespace StepParameters

@[expose] def light (p : StepParameters) : ℕ := if p.wide then 5 else 0
@[expose] def heavy (p : StepParameters) : ℕ := if p.wide then 20 else 15
@[expose] def ordinary (p : StepParameters) : ℕ := 5*p.t+p.e
@[expose] def special (p : StepParameters) : ℕ := p.heavy*p.r+p.light*(p.t-p.r)+p.e
@[expose] def order (p : StepParameters) : ℕ := columns p.wide * (5*p.t) + p.special

end StepParameters

@[expose] def stepValid (n : ℕ) (p : StepParameters) : Prop :=
  p.order = n ∧ (p.e = 1 ∨ p.e = 6) ∧ p.r ≤ p.t ∧ availableArray p.wide p.t ∧
    constructible p.ordinary ∧ constructible p.special ∧ p.ordinary < n ∧ p.special < n

instance (n : ℕ) (p : StepParameters) : Decidable (stepValid n p) := by
  unfold stepValid
  infer_instance

@[expose] def findWeighting (n : ℕ) : StepParameters := Id.run do
  for wide in [false, true] do
    let coefficient := if wide then 90 else 65
    for t in [columns wide : n/(5*columns wide)+1] do
      for e in [1,6] do
        let r := (n-e-coefficient*t)/15
        let p : StepParameters := ⟨wide,t,r,e⟩
        if stepValid n p then return p
  return ⟨false,0,0,0⟩

theorem reduceLarge {n : ℕ} (hn : 8726 ≤ n) (h : constructible n) :
    ∃ p, stepValid n p := by
  obtain ⟨t,r,e,eq,he,cut,ht,cop,ho,hs,lo,ls⟩ := reduceUpper hn h.1
  have array : availableArray false t := ⟨ht, Or.inr (Or.inr (Or.inr (Or.inr cop)))⟩
  refine ⟨⟨false,t,r,e⟩, ?_, he, cut, array, ho, ?_, ?_, ?_⟩ <;>
    simp [StepParameters.order, StepParameters.ordinary, StepParameters.special,
      StepParameters.light, StepParameters.heavy, columns] <;> first | exact hs | omega

private def lightTemplate : (wide : Bool) →
    RowTemplate (columns wide) (if wide then 5 else 0)
  | false => template13light
  | true => template17light

private def heavyTemplate : (wide : Bool) →
    RowTemplate (columns wide) (if wide then 20 else 15)
  | false => template13heavy
  | true => template17heavy

abbrev SmallerDesigns (n : ℕ) :=
  ∀ m < n, constructible m → Nonempty (SteinerSystem (Fin m))

/-- Realize a certified weighting using the two smaller fillings. -/
theorem realizeStep {n : ℕ} {p : StepParameters} (hp : stepValid n p)
    (ih : SmallerDesigns n) :
    Nonempty (SteinerSystem (Fin n)) := by
  obtain ⟨order, shared, cut, ht, ho, hs, lo, ls⟩ := hp
  obtain ⟨A, rows, tr⟩ := availableTransversal ht
  have eq : p.t = p.r + (p.t-p.r) := by omega
  let split : Fin p.t ≃ Fin p.r ⊕ Fin (p.t-p.r) :=
    (finCongr eq).trans finSumFinEquiv.symm
  have td := tr.relabel split
  have ord : Nonempty (SteinerSystem (Fin (5*(p.r+(p.t-p.r))+p.e))) := by
    rw [← eq]
    exact ih _ lo ho
  have light : RowTemplate (columns p.wide) p.light := lightTemplate p.wide
  have heavy : RowTemplate (columns p.wide) p.heavy := heavyTemplate p.wide
  have result := wilsonStep td light heavy shared ord (ih _ ls hs)
  rw [← eq] at result
  have ordEq : columns p.wide * (5*p.t) + (p.heavy*p.r+p.light*(p.t-p.r)) + p.e = n := by
    rw [← order, StepParameters.order, StepParameters.special, Nat.add_assoc]
  rwa [ordEq] at result

structure ProductParameters where
  d : ℕ
  m : ℕ
  e : ℕ

@[expose] def productValid (n : ℕ) (p : ProductParameters) : Prop :=
  p.d*p.m+p.e = n ∧ (p.e = 0 ∨ p.e = 1 ∨ p.e = 6) ∧
  5 ≤ p.m ∧ p.m.Coprime 6 ∧ constructible p.d ∧ constructible (p.m+p.e) ∧
  p.d < n ∧ p.m+p.e < n

instance (n : ℕ) (p : ProductParameters) : Decidable (productValid n p) := by
  unfold productValid
  infer_instance

@[expose] def findProduct (n : ℕ) : ProductParameters := Id.run do
  for e in [0,1,6] do
    for m in [5:(n-e)/6+1] do
      let p : ProductParameters := ⟨(n-e)/m, m, e⟩
      if productValid n p then return p
  return ⟨0,0,0⟩

theorem realizeProduct {n : ℕ} {p : ProductParameters} (hp : productValid n p)
    (ih : SmallerDesigns n) : Nonempty (SteinerSystem (Fin n)) := by
  obtain ⟨d,m,e⟩ := p
  obtain ⟨order, shared, bound, cop, hd, hf, ld, lf⟩ := hp
  change 5 ≤ m at bound
  have : NeZero m := ⟨by omega⟩
  have diffs : ∀ i : Fin 5, i.val ≠ 0 → i.val ∣ (6 : ℕ)^2 := by decide
  have td := modular_transversal (k := 5) (t := m) (fun i hz hi =>
    ((cop.pow_right 2).of_dvd_right (diffs ⟨i,hi⟩ (Nat.ne_of_gt hz))).symm)
  rw [← order]
  exact productStep (by simp : Fintype.card (Fin 5 ⊕ Unit) = 6)
    (td.relabel (ZMod.finEquiv m).toEquiv.symm) (ih _ ld hd).some shared (ih _ lf hf)

end Lemmata.SteinerSixSpectrum
