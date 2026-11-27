module

public import Lemmata.FrankWolfePS.Unique.Transfer
public import Lemmata.FrankWolfePS.Unique.Replay

@[expose] public section

/-!
# The parameters of the jittered family

For simplex scale `A` and a method requiring no more than `T` calls: the jitter scale `η`, the
grid step `b`, the bulge `s`, and the number of grid levels `Q`. The jitter is tiny compared with
the gap `A² / (T + 1)` and with `A` itself; `Q` is large enough that a uniformly random grid
table is bad for the method with probability at most `1/100`.
-/

namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The number of grid levels per coordinate. -/
def alphabet (ι : Type*) [Fintype ι] (T : ℕ) := 1 + 100 * nodes ι T * tests ι

/-- The jitter scale `η = A² / (10⁶ (T + 1) (A + 36)²)`. -/
noncomputable def jitter (A : ℝ) (T : ℕ) : ℝ :=
  A ^ 2 / (1000000 * ((T + 1 : ℕ) : ℝ) * (A + 36) ^ 2)

/-- The grid step. -/
noncomputable def step (A : ℝ) (ι : Type*) [Fintype ι] (T : ℕ) : ℝ :=
  jitter A T / ((dim ι : ℝ) * (alphabet ι T : ℝ))

/-- The bulge of the core. -/
noncomputable def smooth (A : ℝ) (ι : Type*) [Fintype ι] (T : ℕ) : ℝ :=
  step A ι T / (8 * (dim ι : ℝ))

/-- The hidden grid tables. -/
abbrev Draw (ι : Type*) [Fintype ι] (T : ℕ) := Table ι (alphabet ι T)

/-- The jittered vertices of a table. -/
noncomputable def vtx (A : ℝ) (a : ι) (T : ℕ) (D : Draw ι T) := vertices A a (step A ι T) D

/-- The body of the instance `(D, I)`. -/
noncomputable def instanceBody (A : ℝ) (a : ι) (T : ℕ) (D : Draw ι T) (I : Finset ι) :=
  Body (vtx A a T D) (smooth A ι T) I

theorem settings {A : ℝ} (hA : 0 < A) (ι : Type*) [Fintype ι] (T : ℕ) :
    let η := jitter A T
    let b := step A ι T
    let s := smooth A ι T
    let h := 2 * η
    0 < η ∧ 0 < b ∧ 0 < s ∧ (dim ι : ℝ) * (4 * s) < b ∧ η + s ≤ h ∧ h ≤ 1 ∧
      (A + 35) * (2 * A + 5) * h ≤ 4 * A ^ 2 / (1000000 * ((T + 1 : ℕ) : ℝ)) ∧
      2 * h ≤ A / 1000 ∧ (dim ι : ℝ) * b * (alphabet ι T : ℝ) = η := by
  let n : ℝ := dim ι
  let Q : ℝ := alphabet ι T
  have hn : 1 ≤ n := by dsimp [n, dim]; exact_mod_cast Fintype.card_pos (α := Option ι)
  have hQ : 1 ≤ Q := by
    dsimp [Q, alphabet]; exact_mod_cast (by omega : 1 ≤ 1 + 100 * nodes ι T * tests ι)
  let k : ℝ := ((T + 1 : ℕ) : ℝ)
  have k1 : 1 ≤ k := by dsimp [k]; norm_cast; omega
  let P : ℝ := (A + 36) ^ 2
  have P0 : 0 < P := by positivity
  let η := jitter A T
  let b := step A ι T
  let s := smooth A ι T
  have hηP : η * (1000000 * k * P) = A ^ 2 := by
    change A ^ 2 / (1000000 * k * P) * (1000000 * k * P) = A ^ 2; field_simp
  have e0 : 0 < η := by dsimp [η, jitter]; positivity
  have b0 : 0 < b := by change 0 < η / (n * Q); positivity
  have s0 : 0 < s := by change 0 < b / (8 * n); positivity
  have eb : n * b * Q = η := by change n * (η / (n * Q)) * Q = η; field_simp
  have es : n * (4 * s) = b / 2 := by change n * (4 * (b / (8 * n))) = b / 2; field_simp; ring
  have b1 : b ≤ η := by
    change η / (n * Q) ≤ η
    exact div_le_self e0.le (by nlinarith)
  have s1 : s ≤ b := by
    change b / (8 * n) ≤ b
    exact div_le_self b0.le (by nlinarith)
  have AP : A ^ 2 ≤ P := by dsimp [P]; nlinarith
  have AP' : 144 * A ≤ P := by dsimp [P]; nlinarith [_root_.sq_nonneg (A - 36)]
  have bound : (A + 35) * (2 * A + 5) ≤ 2 * P := by dsimp [P]; nlinarith
  refine ⟨e0, b0, s0, es.trans_lt (by linarith), by linarith, ?_, ?_, ?_, eb⟩
  · -- h ≤ 1
    change 2 * η ≤ 1
    nlinarith [mul_le_mul k1 AP (by positivity) (by linarith)]
  · -- the perturbation is small against the gap
    change (A + 35) * (2 * A + 5) * (2 * η) ≤ 4 * A ^ 2 / (1000000 * k)
    rw [le_div_iff₀ (by positivity)]
    have : (A + 35) * (2 * A + 5) * (2 * η) * (1000000 * k) ≤ 2 * P * (2 * η) * (1000000 * k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right bound (by positivity))
        (by positivity)
    nlinarith
  · -- the perturbation is small against the scale
    change 2 * (2 * η) ≤ A / 1000
    have h144 : 144 * A * A ≤ P * A := mul_le_mul_of_nonneg_right AP' hA.le
    nlinarith [mul_le_mul_of_nonneg_left k1 (show 0 ≤ η * P by positivity)]

theorem vtx_near {A : ℝ} (hA : 0 < A) (a : ι) (T : ℕ) (D : Draw ι T) (j : ι) :
    ‖vtx A a T D j - baseV A j‖ ≤ jitter A T := by
  have S := settings hA ι T
  simpa [vtx, vertices, baseV, S.2.2.2.2.2.2.2.2] using grid_norm a S.2.1.le D j

theorem vtx_anchor {A : ℝ} (hA : 0 < A) (a : ι) (T : ℕ) (D : Draw ι T) {R : Finset ι}
    (ha : a ∈ R) : start A a ∈ instanceBody A a T D R := by
  apply anchor_mem ha _ (settings hA ι T).2.2.1.le
  ext c; simp [vtx, vertices, grid, baseV]

theorem bad_table_count {A : ℝ} (hA : 0 < A) (a : ι) (T : ℕ) (ask : Hist ι → Ambient ι) :
    countP (trouble (Q := alphabet ι T) A a (step A ι T) (smooth A ι T) (start A a) ask T {a}
      (fun _ => [])) ≤ (Fintype.card (Draw ι T) : ℝ) / 100 := by
  have S := settings hA ι T
  have H := trouble_count (Q := alphabet ι T) A a S.2.1.le S.2.2.2.1 (start A a) ask T (R := {a})
    (mem_singleton_self a) (h := fun _ => []) (fun _ _ _ => rfl)
  let C := countP (trouble (Q := alphabet ι T) A a (step A ι T) (smooth A ι T) (start A a) ask T
    {a} (fun _ => []))
  let M : ℝ := Fintype.card (Draw ι T)
  let W : ℝ := (nodes ι T : ℝ) * (tests ι : ℝ)
  have eq : (alphabet ι T : ℝ) = 1 + 100 * W := by simp [alphabet, W]; ring
  have cp : 0 ≤ C := sum_nonneg fun _ _ => flag_nonneg _
  change C * (alphabet ι T : ℝ) ≤ W * M at H
  rw [eq] at H
  change C ≤ M / 100
  by_cases w : W = 0
  · rw [w] at H; simp at H; exact H.trans (by dsimp [M]; positivity)
  · have wp : 0 < W := lt_of_le_of_ne (by dsimp [W]; positivity) (Ne.symm w)
    by_contra! no
    nlinarith [mul_pos wp (sub_pos.mpr no)]

end Lemmata.FrankWolfePS.Unique
