module

public import Lemmata.RM59.Proof.Descent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Lemmata.RM59.PlaneGeometry

open scoped BigOperators

def AllTriplePlanes {ι : Type*} (allowed : Point 9 → Point 9 → Prop)
    (p : ι → Point 9) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → allowed (p i + p j) (p i + p k)

def directions {n : Nat} (a b : Point 9) (u : Fin n → Point 9) :
    Fin 2 ⊕ Fin n → Point 9 := Sum.elim ![a, b] u

def simplex {n : Nat} (a b : Point 9) (u : Fin n → Point 9) :
    Option (Fin 2 ⊕ Fin n) → Point 9 := fun i => i.elim 0 (directions a b u)

def Extension (allowed : Point 9 → Point 9 → Prop) (a b x : Point 9) : Prop :=
  x ≠ 0 ∧ x ≠ a ∧ x ≠ b ∧ x ≠ a + b ∧
    allowed a x ∧ allowed b x ∧ allowed (a + b) (a + x)

def ExtensionEdge (allowed : Point 9 → Point 9 → Prop) (a b x y : Point 9) : Prop :=
  AffineIndependent Field ![0, a, b, x, y] ∧
    allowed x y ∧ allowed (a + x) (a + y) ∧ allowed (b + x) (b + y)

theorem directions_linearIndependent {n : Nat} (a b : Point 9) (u : Fin n → Point 9)
    (h : AffineIndependent Field (simplex a b u)) :
    LinearIndependent Field (directions a b u) := by
  have hdiff := (affineIndependent_iff_linearIndependent_vsub Field (simplex a b u) none).mp h
  let inclusion : Fin 2 ⊕ Fin n →
      {i : Option (Fin 2 ⊕ Fin n) // i ≠ none} :=
    fun i => ⟨some i, by simp⟩
  have hinj : Function.Injective inclusion := by
    intro i j hij
    exact Option.some.inj (congrArg Subtype.val hij)
  have hsub := hdiff.comp inclusion hinj
  simpa [inclusion, simplex, Function.comp_def, vsub_eq_sub] using hsub

theorem residual_extension {n : Nat} (allowed : Point 9 → Point 9 → Prop)
    (a b : Point 9) (u : Fin n → Point 9)
    (hAI : AffineIndependent Field (simplex a b u))
    (hplanes : AllTriplePlanes allowed (simplex a b u)) (i : Fin n) :
    Extension allowed a b (u i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have heq := hAI.injective (show
      simplex a b u (some (Sum.inr i)) = simplex a b u none from hzero)
    cases heq
  · intro heq
    have hi := hAI.injective (show
      simplex a b u (some (Sum.inr i)) = simplex a b u (some (Sum.inl 0)) from heq)
    cases hi
  · intro heq
    have hi := hAI.injective (show
      simplex a b u (some (Sum.inr i)) = simplex a b u (some (Sum.inl 1)) from heq)
    cases hi
  · have hLI := directions_linearIndependent a b u hAI
    let anchors : Set (Fin 2 ⊕ Fin n) := {Sum.inl 0, Sum.inl 1}
    have hnot := hLI.notMem_span_image (s := anchors) (x := Sum.inr i) (by simp [anchors])
    intro heq
    apply hnot
    change u i ∈ Submodule.span Field ((directions a b u) '' anchors)
    rw [heq]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨Sum.inl 0, by simp [anchors], rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl 1, by simp [anchors], rfl⟩
  · simpa [simplex, directions] using hplanes none (some (Sum.inl 0))
      (some (Sum.inr i)) (by simp) (by simp) (by simp)
  · simpa [simplex, directions] using hplanes none (some (Sum.inl 1))
      (some (Sum.inr i)) (by simp) (by simp) (by simp)
  · simpa [simplex, directions] using hplanes (some (Sum.inl 0)) (some (Sum.inl 1))
      (some (Sum.inr i)) (by simp) (by simp) (by simp)

theorem residual_edge {n : Nat} (allowed : Point 9 → Point 9 → Prop)
    (a b : Point 9) (u : Fin n → Point 9)
    (hAI : AffineIndependent Field (simplex a b u))
    (hplanes : AllTriplePlanes allowed (simplex a b u))
    (i j : Fin n) (hij : i ≠ j) : ExtensionEdge allowed a b (u i) (u j) := by
  have hfive : AffineIndependent Field ![0, a, b, u i, u j] := by
    let selection : Fin 5 → Option (Fin 2 ⊕ Fin n) :=
      ![none, some (Sum.inl 0), some (Sum.inl 1), some (Sum.inr i), some (Sum.inr j)]
    have hinj : Function.Injective selection := by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> simp_all [selection]
    have hsub := hAI.comp_embedding ⟨selection, hinj⟩
    change AffineIndependent Field (simplex a b u ∘ selection) at hsub
    have heq : simplex a b u ∘ selection = ![0, a, b, u i, u j] := by
      funext r
      fin_cases r <;> rfl
    rw [heq] at hsub
    exact hsub
  refine ⟨hfive, ?_, ?_, ?_⟩
  · simpa [simplex, directions] using hplanes none (some (Sum.inr i))
      (some (Sum.inr j)) (by simp) (by simp) (by simpa using hij)
  · simpa [simplex, directions] using hplanes (some (Sum.inl 0)) (some (Sum.inr i))
      (some (Sum.inr j)) (by simp) (by simp) (by simpa using hij)
  · simpa [simplex, directions] using hplanes (some (Sum.inl 1)) (some (Sum.inr i))
      (some (Sum.inr j)) (by simp) (by simp) (by simpa using hij)

theorem coloring_excludes_simplex {n m : Nat} (allowed : Point 9 → Point 9 → Prop)
    (a b : Point 9) (u : Fin n → Point 9) (color : Point 9 → Fin m) (hm : m < n)
    (hproper : ∀ x y, Extension allowed a b x → Extension allowed a b y →
      ExtensionEdge allowed a b x y → color x ≠ color y)
    (hAI : AffineIndependent Field (simplex a b u))
    (hplanes : AllTriplePlanes allowed (simplex a b u)) : False := by
  have hinj : Function.Injective (fun i : Fin n => color (u i)) := by
    intro i j heq
    by_contra hij
    exact hproper (u i) (u j) (residual_extension allowed a b u hAI hplanes i)
      (residual_extension allowed a b u hAI hplanes j)
      (residual_edge allowed a b u hAI hplanes i j hij) heq
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hcard
  omega

theorem annihilator_excludes_simplex {n k : Nat}
    (allowed : Point 9 → Point 9 → Prop) (a b : Point 9) (u : Fin n → Point 9)
    (annihilator : Point 9 →ₗ[Field] Point k) (hsurj : Function.Surjective annihilator)
    (ha : annihilator a = 0) (hb : annihilator b = 0)
    (hX : ∀ x, Extension allowed a b x → annihilator x = 0)
    (hsize : 9 < 2 + n + k)
    (hAI : AffineIndependent Field (simplex a b u))
    (hplanes : AllTriplePlanes allowed (simplex a b u)) : False := by
  have hzero (i : Fin 2 ⊕ Fin n) : annihilator (directions a b u i) = 0 := by
    rcases i with i | i
    · fin_cases i
      · exact ha
      · exact hb
    · exact hX (u i) (residual_extension allowed a b u hAI hplanes i)
  let v : Fin 2 ⊕ Fin n → LinearMap.ker annihilator :=
    fun i => ⟨directions a b u i, hzero i⟩
  have hLI : LinearIndependent Field v := by
    apply LinearIndependent.of_comp (LinearMap.ker annihilator).subtype
    exact directions_linearIndependent a b u hAI
  have hbound := hLI.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hbound
  have hdim := annihilator.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hdim
  simp only [finrank_top, Point, Module.finrank_fin_fun] at hdim
  simp only [Point] at hbound
  omega

theorem annihilator_surjective_of_rightInverse {k : Nat}
    (annihilator : Point 9 →ₗ[Field] Point k) (sectionMap : Point k →ₗ[Field] Point 9)
    (h : annihilator.comp sectionMap = LinearMap.id) :
    Function.Surjective annihilator := by
  intro y
  refine ⟨sectionMap y, ?_⟩
  exact congrArg (fun f : Point k →ₗ[Field] Point k => f y) h

theorem allTriplePlanes_translate {ι : Type*} (allowed : Point 9 → Point 9 → Prop)
    (p : ι → Point 9) (t : Point 9) :
    AllTriplePlanes allowed (fun i => p i + t) ↔ AllTriplePlanes allowed p := by
  have hsum (x y : Point 9) : (x + t) + (y + t) = x + y := by
    funext i
    change (x i + t i) + (y i + t i) = x i + y i
    calc
      _ = (x i + y i) + (t i + t i) := by ac_rfl
      _ = _ := by rw [field_add_self, add_zero]
  simp only [AllTriplePlanes, hsum]

end Lemmata.RM59.PlaneGeometry
