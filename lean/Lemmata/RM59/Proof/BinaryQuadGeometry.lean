module

public import Lemmata.RM59.Proof.Model
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Lemmata.RM59.BinaryQuadGeometry

open scoped BigOperators Matrix

def quad {m : Nat} (a b t : Point m) : Finset (Point m) := {0, a, b, a + b + t}

def sumFour {m : Nat} (p : Fin 4 → Point m) : Point m := p 0 + p 1 + p 2 + p 3

theorem point_add_self {m : Nat} (x : Point m) : x + x = 0 := by
  funext i
  exact field_add_self _

theorem point_neg_self {m : Nat} (x : Point m) : -x = x := by
  funext i
  exact CharTwo.neg_eq _

def e (i : Fin 3) : Point 3 := Pi.single i 1

theorem clearing_model : ∀ α β : Field,
    quad (e 0 + α • e 2) (e 1 + β • e 2) (e 2) =
      (quad (e 0) (e 1) (e 2)).image
        (fun x => x + (β • e 0 + α • e 1 + (α * β) • e 2)) := by decide

theorem clear_translation {m : Nat} (a b t : Point m) (α β : Field) :
    quad (a + α • t) (b + β • t) t =
      (quad a b t).image (fun x => x + (β • a + α • b + (α * β) • t)) := by
  let f := Fintype.linearCombination Field ![a, b, t]
  have h := congrArg (Finset.image f) (clearing_model α β)
  simpa [quad, Finset.image_image, Function.comp_def, f, e,
    Fintype.linearCombination_apply_single] using h

theorem triple_sum_model :
    LinearIndependent Field ![e 0, e 1, e 0 + e 1 + e 2] := by
  rw [Fintype.linearIndependent_iff]
  decide

theorem pair_shift_model : ∀ α β : Field,
    LinearIndependent Field ![e 0 + α • e 2, e 1 + β • e 2] := by
  simp only [Fintype.linearIndependent_iff]
  decide

theorem mapped_independent {m k : Nat} (v : Fin 3 → Point m)
    (hv : LinearIndependent Field v) (w : Fin k → Point 3)
    (hw : LinearIndependent Field w) :
    LinearIndependent Field (fun i => Fintype.linearCombination Field v (w i)) := by
  have hinj := (linearIndependent_iff_injective_fintypeLinearCombination).mp hv
  exact hw.map' (Fintype.linearCombination Field v) (LinearMap.ker_eq_bot.mpr hinj)

theorem shifted_pair_independent {m : Nat} (a b t : Point m)
    (h : LinearIndependent Field ![a, b, t]) (α β : Field) :
    LinearIndependent Field ![a + α • t, b + β • t] := by
  have hi := mapped_independent ![a, b, t] h _ (pair_shift_model α β)
  convert hi using 1
  funext i
  fin_cases i
  · change a + α • t = Fintype.linearCombination Field ![a, b, t] (e 0 + α • e 2)
    simp [map_add, map_smul, e, Fintype.linearCombination_apply_single]
  · change b + β • t = Fintype.linearCombination Field ![a, b, t] (e 1 + β • e 2)
    simp [map_add, map_smul, e, Fintype.linearCombination_apply_single]

theorem sum_scalar : ∀ a b c d : Field, (a + b) + (a + c) + (a + d) = a + b + c + d := by
  decide

theorem fourth_scalar : ∀ a b c d : Field,
    ((a + b) + (a + c) + (a + b + c + d)) + a = d := by decide

theorem directions_sum {m : Nat} (p : Fin 4 → Point m) :
    (p 0 + p 1) + (p 0 + p 2) + (p 0 + p 3) = sumFour p := by
  funext i
  exact sum_scalar (p 0 i) (p 1 i) (p 2 i) (p 3 i)

theorem quadruple_translate {m : Nat} (p : Fin 4 → Point m) :
    (Finset.univ.image p) =
      (quad (p 0 + p 1) (p 0 + p 2) (sumFour p)).image (fun x => x + p 0) := by
  have h1 : (p 0 + p 1) + p 0 = p 1 := by
    calc
      _ = (p 0 + p 0) + p 1 := by ac_rfl
      _ = _ := by rw [point_add_self, zero_add]
  have h2 : (p 0 + p 2) + p 0 = p 2 := by
    calc
      _ = (p 0 + p 0) + p 2 := by ac_rfl
      _ = _ := by rw [point_add_self, zero_add]
  have h3 : ((p 0 + p 1) + (p 0 + p 2) + sumFour p) + p 0 = p 3 := by
    funext i
    exact fourth_scalar (p 0 i) (p 1 i) (p 2 i) (p 3 i)
  simp only [quad, Finset.image_insert, Finset.image_singleton, zero_add, h1, h2, h3]
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

theorem independent_sum_directions {m : Nat} (p : Fin 4 → Point m)
    (hp : AffineIndependent Field p) :
    LinearIndependent Field ![p 0 + p 1, p 0 + p 2, sumFour p] := by
  have hd := (affineIndependent_iff_linearIndependent_vsub Field p 0).mp hp
  let select : Fin 3 → {i : Fin 4 // i ≠ 0} :=
    fun j => ⟨j.succ, Fin.succ_ne_zero j⟩
  have hinj : Function.Injective select := by
    intro i j h
    exact (Fin.succ_injective 3) (congrArg Subtype.val h)
  have h0 := hd.comp select hinj
  have hv : LinearIndependent Field ![p 0 + p 1, p 0 + p 2, p 0 + p 3] := by
    convert h0 using 1
    funext j
    fin_cases j <;> simp [select, Function.comp_def, vsub_eq_sub, sub_eq_add_neg, point_neg_self,
      add_comm] <;> ac_rfl
  have hi := mapped_independent ![p 0 + p 1, p 0 + p 2, p 0 + p 3] hv _ triple_sum_model
  convert hi using 1
  funext j
  fin_cases j
  · change p 0 + p 1 = Fintype.linearCombination Field
      ![p 0 + p 1, p 0 + p 2, p 0 + p 3] (e 0)
    simp [e, Fintype.linearCombination_apply_single]
  · change p 0 + p 2 = Fintype.linearCombination Field
      ![p 0 + p 1, p 0 + p 2, p 0 + p 3] (e 1)
    simp [e, Fintype.linearCombination_apply_single]
  · change sumFour p = Fintype.linearCombination Field
      ![p 0 + p 1, p 0 + p 2, p 0 + p 3] (e 0 + e 1 + e 2)
    simp [map_add, e, Fintype.linearCombination_apply_single, directions_sum]

end Lemmata.RM59.BinaryQuadGeometry
