module

public import Lemmata.OracleComplexity.Cube

@[expose] public section

/-!
# Values of the first deviations from the greedy path

For a point `z` and `k < M`, `devVal M z k` is the value at `z` of the hard function of the string
that follows the greedy path towards `z` below bit `k` and leaves it at bit `k`; `devVal M z M` is
the value of the path itself. Every string that first leaves the path at bit `k` has this value at
`z`, the values decrease in `k`, and every string that follows the path below bit `h` has value at
most `devVal M z h`.
-/

namespace Lemmata.OracleComplexity

variable {M : ℕ}

/-- The value of the first deviation at bit `k` (or of the path, for `k ≥ M`). -/
noncomputable def devVal (M : ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  if k < M then boxFn (boxFill M z (some k)) z else boxFn (boxFill M z none) z

theorem fill_pre (z : ℝ) (k : ℕ) :
    ∀ i : Fin M, (i : ℕ) < k → boxFill M z (some k) i = pathBit z i := by
  intro i hi
  simp [boxFill, hi]

theorem fill_dev (z : ℝ) {k : ℕ} (hk : k < M) : boxFill M z (some k) ⟨k, hk⟩ ≠ pathBit z k := by
  simp [boxFill]

/-- A string that first leaves the path at bit `k` gets the oracle answer of the filled string. -/
theorem oracle_of_first_dev {U : Fin M → Bool} {z : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → U i = pathBit z i) (hdev : U ⟨k, hk⟩ ≠ pathBit z k) :
    boxOracle U z = boxOracle (boxFill M z (some k)) z := by
  refine oracle_congr_of_deviate hk hpre hdev (fill_pre z k) (fill_dev z hk) (fun i hi => ?_)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [hpre i h, fill_pre z k i h]
  · have hi' : i = ⟨k, hk⟩ := Fin.ext h
    subst hi'
    have hF : boxFill M z (some k) ⟨k, hk⟩ = !pathBit z k := by simp [boxFill]
    rw [hF]
    cases hU : U ⟨k, hk⟩ <;> cases hp : pathBit z k <;> simp_all

theorem value_of_first_dev {U : Fin M → Bool} {z : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → U i = pathBit z i) (hdev : U ⟨k, hk⟩ ≠ pathBit z k) :
    boxFn U z = devVal M z k := by
  have := congrArg Prod.fst (oracle_of_first_dev hk hpre hdev)
  simp only [boxOracle] at this
  rw [this, devVal, ite_eq_left hk]

theorem value_of_path {U : Fin M → Bool} {z : ℝ} (h : ∀ i : Fin M, U i = pathBit z i) :
    boxFn U z = devVal M z M := by
  have hU : U = boxFill M z none := funext h
  rw [hU, devVal, ite_eq_right (lt_irrefl M)]

theorem path_step_dist {T : Fin M → Bool} {z : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k + 1 → T i = pathBit z i) :
    |z - boxCenter T (k + 1)| = abs (|z - pathCenter z k| - (1 / 4) ^ (k + 1)) := by
  rw [boxCenter_succ T hk, center_of_path k hk.le (fun i hi => hpre i (by omega)),
    hpre ⟨k, hk⟩ (by simp)]
  unfold pathBit
  by_cases h : pathCenter z k < z
  · simp only [h, decide_true, bitSign, ite_true]
    rw [abs_of_pos (by linarith : 0 < z - pathCenter z k)]
    congr 1
    ring
  · simp only [h, decide_false, bitSign, Bool.false_eq_true, ite_false]
    push Not at h
    rw [abs_of_nonpos (by linarith : z - pathCenter z k ≤ 0), ← abs_neg]
    congr 1
    ring

theorem dev_step_dist {T : Fin M → Bool} {z : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → T i = pathBit z i) (hdev : T ⟨k, hk⟩ ≠ pathBit z k) :
    |z - boxCenter T (k + 1)| = |z - pathCenter z k| + (1 / 4) ^ (k + 1) := by
  rw [boxCenter_succ T hk, center_of_path k hk.le hpre]
  have hq : (0 : ℝ) < (1 / 4) ^ (k + 1) := by positivity
  unfold pathBit at hdev
  by_cases h : pathCenter z k < z
  · have hT : T ⟨k, hk⟩ = false := by
      cases hT : T ⟨k, hk⟩
      · rfl
      · exact absurd (by rw [hT]; simp [h]) hdev
    rw [hT]
    simp only [bitSign, Bool.false_eq_true, ite_false]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    ring
  · push Not at h
    have hT : T ⟨k, hk⟩ = true := by
      cases hT : T ⟨k, hk⟩
      · exact absurd (by rw [hT]; simp [not_lt.mpr h]) hdev
      · rfl
    rw [hT]
    simp only [bitSign, ite_true]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

/-- The values of the first deviations decrease. -/
theorem devVal_succ_le (z : ℝ) {k : ℕ} (hk : k + 1 ≤ M) : devVal M z (k + 1) ≤ devVal M z k := by
  have hkM : k < M := by omega
  set F := boxFill M z (some k) with hF
  have hFv : devVal M z k = boxFn F z := by rw [devVal, ite_eq_left hkM]
  set F' := boxFill M z (if k + 1 < M then some (k + 1) else none) with hF'
  have hF'v : devVal M z (k + 1) = boxFn F' z := by
    rw [devVal, hF']
    split_ifs <;> rfl
  have hF'pre : ∀ i : Fin M, (i : ℕ) < k + 1 → F' i = pathBit z i := by
    intro i hi
    rw [hF']
    split_ifs
    · exact fill_pre z (k + 1) i hi
    · rfl
  rw [hFv, hF'v]
  have hq0 : (0 : ℝ) < (1 / 4) ^ (k + 1) := by positivity
  have hdF := dev_step_dist hkM (fill_pre z k) (fill_dev z hkM)
  have hdF' := path_step_dist hkM hF'pre
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    have := abs_add_le a (-b)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have hpiece_k1 : boxPiece F' (k + 1) z ≤ boxPiece F (k + 1) z := by
    unfold boxPiece
    rw [hdF, hdF']
    have h1 : abs (|z - pathCenter z k| - (1 / 4) ^ (k + 1)) ≤
        |z - pathCenter z k| + (1 / 4) ^ (k + 1) := by
      have := habs (|z - pathCenter z k|) ((1 / 4) ^ (k + 1))
      rwa [abs_abs, abs_of_pos hq0] at this
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (k + 1))
    linarith
  apply Finset.sup'_le
  intro j hj
  have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  show boxPiece F' j z ≤ boxFn F z
  rcases lt_trichotomy j (k + 1) with hjk | hjk | hjk
  · have h1 : boxPiece F' j z = boxPiece F j z :=
      (boxPiece_congr (fun i hi => (hF'pre i (by omega)).trans
        (fill_pre z k i (by omega)).symm) z).1
    rw [h1]
    exact piece_le_fn F hjM z
  · subst hjk
    exact hpiece_k1.trans (piece_le_fn F hjM z)
  · -- deeper pieces of the deviation at `k + 1`
    have hk1 : k + 1 < M := by omega
    have hF'eq : F' = boxFill M z (some (k + 1)) := by rw [hF', ite_eq_left hk1]
    rw [hF'eq] at hF'pre ⊢
    have hdev' := fill_dev z hk1
    have hle : boxPiece (boxFill M z (some (k + 1))) j z ≤
        boxPiece (boxFill M z (some (k + 1))) (k + 2) z := by
      rcases Nat.lt_or_ge (k + 2) j with h | h
      · exact (deep_facts hk1 (fill_pre z (k + 1)) hdev' j (by omega) hjM).1
      · have : j = k + 2 := by omega
        rw [this]
    refine hle.trans (le_trans ?_ (piece_le_fn F hk z))
    -- `D_{k+1} ≤ D_k`
    have hd2 := dev_step_dist hk1 (fill_pre z (k + 1)) hdev'
    have hpc := path_step_dist hkM (T := boxFill M z none) (fun i _ => rfl)
    rw [center_of_path (S := boxFill M z none) (x := z) (k + 1) hk1.le (fun i _ => rfl)] at hpc
    show boxPiece (boxFill M z (some (k + 1))) (k + 1 + 1) z ≤ boxPiece F (k + 1) z
    unfold boxPiece
    set q : ℝ := (1 / 4) ^ (k + 1) with hq
    rw [hd2, hpc, hdF]
    have e1 : boxLevel (k + 1 + 1) = boxLevel (k + 1) - 1 / 2 * (1 / 8) ^ (k + 1) :=
      boxLevel_succ (k + 1)
    rw [e1]
    have e2 : (1 / 8 : ℝ) ^ (k + 1) = (1 / 2) ^ (k + 1) * q := by rw [hq, ← mul_pow]; norm_num
    have e3 : (1 / 8 : ℝ) ^ (k + 1 + 1) = (1 / 8) ^ (k + 1) / 8 := by rw [pow_succ]; ring
    have e4 : (1 / 2 : ℝ) ^ (k + 1 + 1) = (1 / 2) ^ (k + 1) / 2 := by rw [pow_succ]; ring
    have e5 : (1 / 4 : ℝ) ^ (k + 1 + 1) = q / 4 := by rw [hq, pow_succ]; ring
    rw [e3, e4, e5, e2]
    have hr0 : 0 ≤ |z - pathCenter z k| := abs_nonneg _
    have hkey : abs (|z - pathCenter z k| - q) - q ≤ 2 * |z - pathCenter z k| := by
      have := habs (|z - pathCenter z k|) q
      rw [abs_abs, abs_of_pos hq0] at this
      linarith
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) / 2)
    nlinarith

theorem devVal_anti (z : ℝ) : ∀ d h, h + d ≤ M → devVal M z (h + d) ≤ devVal M z h := by
  intro d
  induction d with
  | zero => intro h _; exact le_rfl
  | succ d ih =>
    intro h hd
    exact (devVal_succ_le z (k := h + d) (by omega)).trans (ih h (by omega))

/-- A string that follows the path below bit `h` has value at most `devVal M z h`. -/
theorem value_le_of_prefix {U : Fin M → Bool} {z : ℝ} {h : ℕ} (hh : h ≤ M)
    (hpre : ∀ i : Fin M, (i : ℕ) < h → U i = pathBit z i) : boxFn U z ≤ devVal M z h := by
  classical
  by_cases hall : ∀ i : Fin M, U i = pathBit z i
  · rw [value_of_path hall]
    have := devVal_anti (M := M) z (M - h) h (by omega)
    rwa [show h + (M - h) = M by omega] at this
  · push Not at hall
    have hex : ∃ k, ∃ hk : k < M, U ⟨k, hk⟩ ≠ pathBit z k := by
      obtain ⟨i, hi⟩ := hall
      exact ⟨i, i.2, hi⟩
    set k := Nat.find hex with hkdef
    obtain ⟨hkM, hkdev⟩ := Nat.find_spec hex
    have hmin : ∀ i : Fin M, (i : ℕ) < k → U i = pathBit z i := by
      intro i hi
      by_contra hne
      exact Nat.find_min hex hi ⟨i.2, hne⟩
    have hhk : h ≤ k := by
      by_contra hlt
      push Not at hlt
      exact hkdev (hpre ⟨k, hkM⟩ hlt)
    rw [value_of_first_dev hkM hmin hkdev]
    have := devVal_anti (M := M) z (k - h) h (by omega)
    rwa [show h + (k - h) = k by omega] at this

end Lemmata.OracleComplexity
