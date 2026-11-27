module
public import Lemmata.FrankWolfePS.Unique.Geometry
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
noncomputable def countP {A : Type*} [Fintype A] (P : A → Prop) : ℝ := ∑ a, flag (P a)

theorem count_false {A : Type*} [Fintype A] : countP (fun _ : A => False) = 0 := by
  simp [countP, flag]

theorem count_union {A : Type*} [Fintype A] (P Q : A → Prop) :
    countP (fun a => P a ∨ Q a) ≤ countP P + countP Q := by
  classical
  unfold countP; rw [← sum_add_distrib]; apply sum_le_sum; intro a _
  by_cases h : P a <;> by_cases g : Q a <;> simp [flag, h, g]

theorem count_exists {A B : Type*} [Fintype A] [Fintype B] (P : B → A → Prop) :
    countP (fun a => ∃ b, P b a) ≤ ∑ b, countP (P b) := by
  classical
  unfold countP; rw [sum_comm]; apply sum_le_sum; intro a _
  by_cases h : ∃ b, P b a
  · obtain ⟨b, hb⟩ := h
    have H := single_le_sum (f := fun b => flag (P b a)) (fun b _ => flag_nonneg _) (mem_univ b)
    simpa [flag, hb, show ∃ b, P b a from ⟨b, hb⟩] using H
  · simp only [flag, ite_eq_right h]; exact sum_nonneg fun _ _ => by split <;> norm_num

/-- If fixing every field but one allows at most one bad value, the bad
fraction is at most the reciprocal of the alphabet size. -/
theorem fiber_count {C F : Type*} [Fintype C] [DecidableEq C] [Fintype F]
    (c : C) (P : (C → F) → Prop)
    (one : ∀ d e, P d → P e → (∀ i, i ≠ c → d i = e i) → d c = e c) :
    countP P * (Fintype.card F : ℝ) ≤ Fintype.card (C → F) := by
  classical
  let B := (univ : Finset (C → F)).filter P
  have inj : Function.Injective (fun p : (↥B) × F => Function.update p.1.val c p.2) := by
    rintro ⟨⟨d, hd⟩, a⟩ ⟨⟨e, he⟩, b⟩ eq
    have same (i) (hi : i ≠ c) : d i = e i := by
      simpa [Function.update_of_ne hi] using congrFun eq i
    have hc := one d e (mem_filter.mp hd).2 (mem_filter.mp he).2 same
    have de : d = e := funext (fun i => by by_cases hi : i = c; exact hi ▸ hc; exact same i hi)
    have ab : a = b := by simpa using congrFun eq c
    subst e; subst b; rfl
  have H := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_prod, Fintype.card_coe] at H
  have e : countP P = (B.card : ℝ) := by simp [countP, flag, B, sum_boole]
  rw [e]; exact_mod_cast H

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Cell (ι : Type*) := ι × Option ι
abbrev Table (ι : Type*) (Q : ℕ) := Cell ι → Fin Q
def dim (ι : Type*) [Fintype ι] := Fintype.card (Option ι)
noncomputable def grid {Q : ℕ} (a : ι) (b : ℝ) (D : Table ι Q) (j : ι) : Ambient ι :=
  WithLp.toLp 2 (fun c => if j = a then 0 else b * ((D (j, c)).val : ℝ))
/-- The jittered vertices: `(A e_j, 1)` plus the grid offset of label `j` (zero for the anchor). -/
noncomputable def vertices {Q : ℕ} (A : ℝ) (a : ι) (b : ℝ) (D : Table ι Q) (j : ι) :
    Ambient ι :=
  embed (A • atom j, 1) + grid a b D j

omit [DecidableEq ι] in
theorem norm_le_sum (p : Ambient ι) : ‖p‖ ≤ ∑ i, |p i| := by
  have h := sum_sq_le_sq_sum_of_nonneg (s := univ) (f := fun i => |p i|) (fun i _ => abs_nonneg _)
  rw [show ∑ i, |p i| ^ 2 = ‖p‖ ^ 2 by simp [EuclideanSpace.norm_sq_eq]] at h
  nlinarith [sum_nonneg (s := univ) (f := fun i => |p i|) (fun _ _ => abs_nonneg _), norm_nonneg p]

omit [DecidableEq ι] in
theorem large_coordinate (p : Ambient ι) (hp : ‖p‖ = 1) :
    ∃ c, 1 ≤ (dim ι : ℝ) * |p c| := by
  classical
  by_contra! no
  have s := sum_lt_sum_of_nonempty (s := (univ : Finset (Option ι))) univ_nonempty (fun i _ => no i)
  simp only [← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one] at s
  have k : 0 < (dim ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := norm_le_sum p
  rw [hp] at h
  change (dim ι : ℝ) * _ < (dim ι : ℝ) at s
  nlinarith [mul_le_mul_of_nonneg_left h k.le]

theorem grid_norm {Q : ℕ} (a : ι) {b : ℝ} (hb : 0 ≤ b) (D : Table ι Q) (j : ι) :
    ‖grid a b D j‖ ≤ (dim ι : ℝ) * b * Q := by
  have h (c : Option ι) : |grid a b D j c| ≤ b * Q := by
    change abs (if j = a then 0 else b * ((D (j, c)).val : ℝ)) ≤ b * (Q : ℝ)
    split
    · simp; positivity
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (D (j, c)).isLt.le) hb
  have H := sum_le_sum (s := univ) (fun c _ => h c)
  simp only [sum_const, card_univ, nsmul_eq_mul] at H
  exact (norm_le_sum _).trans (by simpa [dim, mul_assoc] using H)

omit [Fintype ι] in
theorem vertex_same {Q : ℕ} (A : ℝ) (a : ι) (b : ℝ) {D F : Table ι Q} {j : ι}
    (h : ∀ c, D (j, c) = F (j, c)) : vertices A a b D j = vertices A a b F j := by
  unfold vertices; congr 1; ext c; simp [grid, h]

theorem vertex_diff {Q : ℕ} (A : ℝ) (a : ι) (b : ℝ) {D F : Table ι Q} {j : ι} {c : Option ι}
    (hj : j ≠ a) (away : ∀ t, t ≠ (j, c) → D t = F t) (p : Ambient ι) :
    ⟪p, vertices A a b D j⟫ - ⟪p, vertices A a b F j⟫ =
      p c * b * (((D (j, c)).val : ℝ) - ((F (j, c)).val : ℝ)) := by
  have e : vertices A a b D j - vertices A a b F j =
      EuclideanSpace.single c (b * (((D (j, c)).val : ℝ) - ((F (j, c)).val : ℝ))) := by
    ext k; by_cases eq : k = c
    · subst k; simp [vertices, grid, hj]; ring
    · have hk : (j, k) ≠ (j, c) := by simpa using eq
      simp [vertices, grid, hj, away _ hk, EuclideanSpace.single, eq]
  rw [← inner_sub_right, e, EuclideanSpace.inner_single_right]; simp; ring
end Lemmata.FrankWolfePS.Unique
