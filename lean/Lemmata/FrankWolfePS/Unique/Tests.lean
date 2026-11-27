module
public import Lemmata.FrankWolfePS.Unique.Grid
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Finset
open scoped RealInnerProductSpace BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : ℕ}

def Local {X : Type*} (R : Finset ι) (f : Table ι Q → X) :=
  ∀ D F, (∀ j ∈ R, ∀ c, D (j, c) = F (j, c)) → f D = f F

abbrev Probe (ι : Type*) := ι × ι × Option ι
def tests (ι : Type*) [Fintype ι] := Fintype.card (Probe ι)

def Test (A : ℝ) (a : ι) (b s : ℝ) (R : Finset ι) (q : Table ι Q → Ambient ι) (k : Probe ι)
    (D : Table ι Q) : Prop :=
  let i := k.1
  let j := k.2.1
  let c := k.2.2
  let p := unit (q D)
  j ∉ R ∧ i ≠ j ∧ q D ≠ 0 ∧ 1 ≤ (dim ι : ℝ) * |p c| ∧ |⟪p, vertices A a b D i⟫ - ⟪p,
      vertices A a b D j⟫| ≤ 2 * s

theorem test_count (A : ℝ) (a : ι) {b s : ℝ} (hb : 0 ≤ b) (small : (dim ι : ℝ) * (4 * s) < b)
    {R : Finset ι} (ha : a ∈ R) {q : Table ι Q → Ambient ι} (loc : Local R q) (k : Probe ι) :
    countP (Test A a b s R q k) * (Q : ℝ) ≤ Fintype.card (Table ι Q) := by
  classical
  obtain ⟨i, j, c⟩ := k
  apply le_trans (b := countP (Test A a b s R q (i, j, c)) * (Fintype.card (Fin Q) : ℝ))
  · simp
  apply fiber_count (j, c)
  intro D F hD hF away
  obtain ⟨hj, hij, _, large, near⟩ := hD
  obtain ⟨_, _, _, _, near'⟩ := hF
  have hj' : j ≠ a := by rintro rfl; contradiction
  have eq : q D = q F :=
      loc D F (fun l hl k =>
          away _ (by rintro eq; exact hj ((show l = j from congrArg Prod.fst eq) ▸ hl)))
  let p := unit (q D)
  have hi : vertices A a b D i = vertices A a b F i :=
    vertex_same A a b (fun k => away _ (fun h => hij (congrArg Prod.fst h)))
  rw [← eq, ← hi] at near'
  change 1 ≤ (dim ι : ℝ) * |p c| at large
  have bound : |⟪p, vertices A a b D j⟫ - ⟪p, vertices A a b F j⟫| ≤ 4 * s := by
    rw [abs_le] at near near' ⊢; dsimp [p]; constructor <;> linarith
  rw [vertex_diff A a b hj' away p, abs_mul, abs_mul, abs_of_nonneg hb] at bound
  by_contra ne
  have nv : (D (j, c)).val ≠ (F (j, c)).val := fun h => ne (Fin.ext h)
  have sep : 1 ≤ |((D (j, c)).val : ℝ) - ((F (j, c)).val : ℝ)| := by
    rcases lt_or_gt_of_ne nv with h|h
    · have H : ((D (j, c)).val : ℝ) + 1 ≤ (F (j, c)).val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have H : ((F (j, c)).val : ℝ) + 1 ≤ (D (j, c)).val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have a1 := mul_le_mul_of_nonneg_right large hb
  have a2 := mul_le_mul_of_nonneg_left sep (by positivity : 0 ≤ (dim ι : ℝ) * abs (p c) * b)
  have a3 := mul_le_mul_of_nonneg_left bound (by positivity : 0 ≤ (dim ι : ℝ))
  nlinarith only [a1, a2, a3, small]

theorem node_count (A : ℝ) (a : ι) {b s : ℝ} (hb : 0 ≤ b) (small : (dim ι : ℝ) * (4 * s) < b)
    {R : Finset ι} (ha : a ∈ R) {q : Table ι Q → Ambient ι} (loc : Local R q) :
    countP (fun D => ∃ k, Test A a b s R q k D) * (Q : ℝ) ≤
        (tests ι : ℝ) * Fintype.card (Table ι Q) := by
  have h := mul_le_mul_of_nonneg_right (count_exists (Test A a b s R q)) (Nat.cast_nonneg Q)
  rw [sum_mul] at h
  have H := sum_le_sum (s := (univ : Finset (Probe ι)))
    (fun k _ => test_count A a hb small ha loc k)
  exact h.trans (by simpa [tests] using H)
end Lemmata.FrankWolfePS.Unique
