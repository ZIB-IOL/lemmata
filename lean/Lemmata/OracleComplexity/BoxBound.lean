module

public import Lemmata.OracleComplexity.Box

@[expose] public section

/-!
# The one-dimensional lower bound

The greedy path towards a query point `x` moves from the current center a quarter of the radius
towards `x`. Asking the string guessing oracle for the bits of this path reveals the first bit `k`
where the hidden string `S` leaves it. Then `x` lies outside the interval of the first `k + 1` bits
of `S`, all deeper pieces lie below the piece of depth `k + 1` at `x`, and the oracle answer depends
only on these `k + 1` bits, which the answer reveals (Lemma IV.5). An `ε`-minimizer of `boxFn S`
with `ε < 8^{-M}` lies within `4^{-M}` of `c_M(S)`, and its greedy path spells out `S`
(Lemma IV.3). Composing an optimization algorithm with the emulation and the decoding gives a
string guessing algorithm with the same number of queries, and Proposition III.3 applies
(Theorem IV.2).
-/

namespace Lemmata.OracleComplexity

open Real

/-- The centers of the greedy path towards `x`. -/
noncomputable def pathCenter (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => pathCenter x i + bitSign (decide (pathCenter x i < x)) * (1 / 4) ^ (i + 1)

/-- The bits of the greedy path towards `x`. -/
noncomputable def pathBit (x : ℝ) (i : ℕ) : Bool := decide (pathCenter x i < x)

variable {M : ℕ}

/-- Strings that follow the greedy path have their centers on it. -/
theorem center_of_path {S : Fin M → Bool} {x : ℝ} : ∀ j ≤ M,
    (∀ i : Fin M, (i : ℕ) < j → S i = pathBit x i) → boxCenter S j = pathCenter x j := by
  intro j
  induction j with
  | zero => intro _ _; simp [boxCenter, pathCenter]
  | succ j ih =>
    intro hj h
    rw [boxCenter_succ S (by omega : j < M), ih (by omega) (fun i hi => h i (by omega)),
      h ⟨j, by omega⟩ (by simp)]
    rfl

/-- The greedy path towards a point within `4^{-M}` of `c_M(S)` spells out `S`. -/
theorem path_of_near {S : Fin M → Bool} {x : ℝ} (hx : |x - boxCenter S M| < (1 / 4) ^ M) :
    ∀ i : Fin M, pathBit x i = S i := by
  have key : ∀ n, n ≤ M → ∀ i : Fin M, (i : ℕ) < n → S i = pathBit x i := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact ih (by omega) i h
      · have hpre := ih (by omega)
        have hnM : n < M := by omega
        have hc := center_of_path n (by omega) hpre
        have htail := boxCenter_tail S (M - (n + 1)) (n + 1) (by omega)
        have h4 : (1 / 4 : ℝ) ^ M ≤ (1 / 4) ^ (n + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hnear : |x - boxCenter S (n + 1)| < (1 / 4) ^ (n + 1) := by
          calc |x - boxCenter S (n + 1)|
              ≤ |x - boxCenter S M| + |boxCenter S M - boxCenter S (n + 1)| := abs_sub_le _ _ _
            _ < (1 / 4) ^ M + ((1 / 4) ^ (n + 1) - (1 / 4) ^ M) / 3 := by linarith
            _ ≤ (1 / 4) ^ (n + 1) := by linarith
        rw [boxCenter_succ S hnM, hc] at hnear
        have hi' : i = ⟨n, hnM⟩ := Fin.ext h
        subst hi'
        unfold pathBit
        cases hS : S ⟨n, hnM⟩
        · rw [hS] at hnear
          simp only [bitSign, Bool.false_eq_true, ite_false] at hnear
          have := (abs_lt.mp hnear).2
          symm
          simp only [decide_eq_false_iff_not, not_lt]
          linarith
        · rw [hS] at hnear
          simp only [bitSign, ite_true] at hnear
          have := (abs_lt.mp hnear).1
          symm
          simp only [decide_eq_true_eq]
          linarith
  intro i
  exact (key M le_rfl i i.2).symm

theorem box_min (S : Fin M → Bool) (y : ℝ) : boxLevel M - (1 / 8) ^ M ≤ boxFn S y := by
  have h := piece_le_fn S le_rfl y
  have hp : boxPiece S M y = boxLevel M - (1 / 8) ^ M + (1 / 2) ^ M * |y - boxCenter S M| := rfl
  have : 0 ≤ (1 / 2 : ℝ) ^ M * |y - boxCenter S M| := by positivity
  linarith

theorem box_at_center (S : Fin M → Bool) :
    boxFn S (boxCenter S M) = boxLevel M - (1 / 8) ^ M := by
  apply le_antisymm _ (box_min S _)
  apply Finset.sup'_le
  intro j hj
  have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have htail := boxCenter_tail S (M - j) j (by omega)
  show boxPiece S j (boxCenter S M) ≤ boxLevel M - (1 / 8) ^ M
  unfold boxPiece boxLevel
  have e1 : (1 / 8 : ℝ) ^ j = (1 / 2) ^ j * (1 / 4) ^ j := by rw [← mul_pow]; norm_num
  have e2 : (1 / 8 : ℝ) ^ M = (1 / 2) ^ M * (1 / 4) ^ M := by rw [← mul_pow]; norm_num
  have hp : (1 / 2 : ℝ) ^ M ≤ (1 / 2) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjM
  have hq : (1 / 4 : ℝ) ^ M ≤ (1 / 4) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjM
  have k1 := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ (1 / 2) ^ j)
  have k2 : (1 / 2 : ℝ) ^ M * (1 / 4) ^ M ≤ (1 / 2) ^ j * (1 / 4) ^ M :=
    mul_le_mul_of_nonneg_right hp (by positivity)
  have k3 : (1 / 2 : ℝ) ^ M * (1 / 4) ^ M ≤ (1 / 2) ^ j * (1 / 4) ^ j :=
    mul_le_mul hp hq (by positivity) (by positivity)
  rw [e1, e2]
  nlinarith

/-- An `ε`-minimizer with `ε < 8^{-M}` lies within `4^{-M}` of `c_M(S)`. -/
theorem near_of_opt {S : Fin M → Bool} {ε x : ℝ} (hε : ε < (1 / 8) ^ M)
    (hopt : ∀ y, boxFn S x ≤ boxFn S y + ε) : |x - boxCenter S M| < (1 / 4) ^ M := by
  have h1 := hopt (boxCenter S M)
  rw [box_at_center] at h1
  have h2 := piece_le_fn S le_rfl x
  have hp : boxPiece S M x = boxLevel M - (1 / 8) ^ M + (1 / 2) ^ M * |x - boxCenter S M| := rfl
  have e2 : (1 / 8 : ℝ) ^ M = (1 / 2) ^ M * (1 / 4) ^ M := by rw [← mul_pow]; norm_num
  have h3 : (1 / 2 : ℝ) ^ M * |x - boxCenter S M| < (1 / 2) ^ M * (1 / 4) ^ M := by
    rw [e2] at hε
    linarith
  exact lt_of_mul_lt_mul_left h3 (by positivity)

/-- A string that follows the greedy path below bit `k` and leaves it at bit `k`: the point is
outside the interval of its first `k + 1` bits. -/
theorem outside_of_deviate {T : Fin M → Bool} {x : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → T i = pathBit x i) (hdev : T ⟨k, hk⟩ ≠ pathBit x k) :
    (1 / 4) ^ (k + 1) ≤ |x - boxCenter T (k + 1)| := by
  rw [boxCenter_succ T hk, center_of_path k hk.le hpre]
  have hq : (0 : ℝ) < (1 / 4) ^ (k + 1) := by positivity
  unfold pathBit at hdev
  cases hT : T ⟨k, hk⟩
  · rw [hT] at hdev
    have hlt : pathCenter x k < x := by
      by_contra hn
      exact hdev (by simp [hn])
    simp only [bitSign, Bool.false_eq_true, ite_false]
    rw [abs_of_pos (by linarith)]
    linarith
  · rw [hT] at hdev
    have hle : x ≤ pathCenter x k := by
      by_contra hn
      push Not at hn
      exact hdev (by simp [hn])
    simp only [bitSign, ite_true]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Beyond the first deviation at bit `k`: the deeper pieces lie below the piece of depth `k + 1`;
if the string leaves the path to the left they lie strictly below, and if it leaves to the right
their centers lie to the right of `x`. -/
theorem deep_facts {T : Fin M → Bool} {x : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → T i = pathBit x i) (hdev : T ⟨k, hk⟩ ≠ pathBit x k) :
    ∀ j, k + 1 < j → j ≤ M → boxPiece T j x ≤ boxPiece T (k + 1) x ∧
      ((pathBit x k = true ∧ boxPiece T j x < boxPiece T (k + 1) x) ∨
        (pathBit x k = false ∧ x < boxCenter T j ∧ x < boxCenter T (k + 1))) := by
  intro j hj hjM
  have hout := outside_of_deviate hk hpre hdev
  have hle : boxPiece T j x ≤ boxPiece T (k + 1) x := by
    have := (piece_chain T hout (j - (k + 1)) (by omega)).1
    rwa [show k + 1 + (j - (k + 1)) = j by omega] at this
  refine ⟨hle, ?_⟩
  have hc := center_of_path k hk.le hpre
  have hsucc := boxCenter_succ T hk
  have hq : (0 : ℝ) < (1 / 4) ^ (k + 1) := by positivity
  cases hp : pathBit x k
  · -- the string leaves to the right
    right
    refine ⟨rfl, ?_, ?_⟩
    · have hT : T ⟨k, hk⟩ = true := by
        cases hT : T ⟨k, hk⟩
        · exact absurd (hT.trans hp.symm) hdev
        · rfl
      have hxle : x ≤ pathCenter x k := by
        unfold pathBit at hp
        simpa using hp
      have hdiff := boxCenter_diff T (k + 1) (j - (k + 1)) (by omega)
      rw [show k + 1 + (j - (k + 1)) = j by omega] at hdiff
      rw [hsucc, hT, hc] at hdiff
      simp only [bitSign, ite_true] at hdiff
      have h4 : (1 / 4 : ℝ) ^ j ≤ (1 / 4) ^ (k + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h5 := (abs_le.mp hdiff).1
      have h6 : (0 : ℝ) ≤ (1 / 4) ^ j := by positivity
      linarith
    · have hT : T ⟨k, hk⟩ = true := by
        cases hT : T ⟨k, hk⟩
        · exact absurd (hT.trans hp.symm) hdev
        · rfl
      have hxle : x ≤ pathCenter x k := by
        unfold pathBit at hp
        simpa using hp
      rw [hsucc, hT, hc]
      simp only [bitSign, ite_true]
      linarith
  · -- the string leaves to the left
    left
    refine ⟨rfl, ?_⟩
    have hT : T ⟨k, hk⟩ = false := by
      cases hT : T ⟨k, hk⟩
      · rfl
      · exact absurd (hT.trans hp.symm) hdev
    have hlt : pathCenter x k < x := by
      unfold pathBit at hp
      simpa using hp
    -- strictly outside the interval of depth `k + 1`
    have hstrict : (1 / 4) ^ (k + 1) < |x - boxCenter T (k + 1)| := by
      rw [hsucc, hT, hc]
      simp only [bitSign, Bool.false_eq_true, ite_false]
      rw [abs_of_pos (by linarith)]
      linarith
    have hk2 : k + 1 < M := by omega
    have h1 := piece_step_strict T hk2 hstrict
    have hout2 := (piece_step T hk2 hstrict.le).2
    have h2 := (piece_chain T hout2 (j - (k + 2)) (by omega)).1
    rw [show k + 1 + 1 + (j - (k + 2)) = j by omega] at h2
    linarith

open Classical in
/-- Two strings that leave the greedy path at bit `k` and agree up to bit `k` get the same oracle
answer at `x`. -/
theorem oracle_congr_of_deviate {T T' : Fin M → Bool} {x : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → T i = pathBit x i) (hdev : T ⟨k, hk⟩ ≠ pathBit x k)
    (hpre' : ∀ i : Fin M, (i : ℕ) < k → T' i = pathBit x i) (hdev' : T' ⟨k, hk⟩ ≠ pathBit x k)
    (hagree : ∀ i : Fin M, (i : ℕ) < k + 1 → T i = T' i) :
    boxOracle T x = boxOracle T' x := by
  have hk2 : k + 1 ≤ M := hk
  have hsub : Finset.range (k + 2) ⊆ Finset.range (M + 1) := fun j hj =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
  have hne : (Finset.range (k + 2)).Nonempty := Finset.nonempty_range_add_one
  -- the value is the maximum of the pieces up to depth `k + 1`
  have hval : ∀ U : Fin M → Bool, (∀ i : Fin M, (i : ℕ) < k → U i = pathBit x i) →
      U ⟨k, hk⟩ ≠ pathBit x k →
      boxFn U x = (Finset.range (k + 2)).sup' hne (fun j => boxPiece U j x) := by
    intro U hU hU'
    apply le_antisymm
    · apply Finset.sup'_le
      intro j hj
      have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hjk : j ≤ k + 1
      · exact Finset.le_sup' (fun j => boxPiece U j x) (Finset.mem_range.mpr (by omega))
      · exact ((deep_facts hk hU hU' j (by omega) hjM).1).trans
          (Finset.le_sup' (fun j => boxPiece U j x) (Finset.mem_range.mpr (by omega)))
    · exact Finset.sup'_mono _ hsub hne
  have hpiece : ∀ j < k + 2, boxPiece T j x = boxPiece T' j x ∧
      pieceLeft T j x = pieceLeft T' j x ∧ pieceRight T j x = pieceRight T' j x :=
    fun j hj => boxPiece_congr (fun i hi => hagree i (by omega)) x
  have hfn : boxFn T x = boxFn T' x := by
    rw [hval T hpre hdev, hval T' hpre' hdev']
    exact Finset.sup'_congr hne rfl (fun j hj => (hpiece j (Finset.mem_range.mp hj)).1)
  -- the left derivative is attained up to depth `k + 1`
  have hleft : ∀ U : Fin M → Bool, (∀ i : Fin M, (i : ℕ) < k → U i = pathBit x i) →
      U ⟨k, hk⟩ ≠ pathBit x k → boxLeft U x = (Finset.range (k + 2)).inf' hne
        (fun j => if boxPiece U j x = boxFn U x then pieceLeft U j x else 1) := by
    intro U hU hU'
    apply le_antisymm
    · exact Finset.inf'_mono _ hsub hne
    · apply Finset.le_inf'
      intro j hj
      have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      by_cases hjk : j ≤ k + 1
      · exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
      · obtain ⟨hle, hcase⟩ := deep_facts hk hU hU' j (by omega) hjM
        by_cases hact : boxPiece U j x = boxFn U x
        · rcases hcase with ⟨-, hlt⟩ | ⟨-, hxj, hxk⟩
          · have := piece_le_fn U hk2 x
            linarith
          · have hact' : boxPiece U (k + 1) x = boxFn U x :=
              le_antisymm (piece_le_fn U hk2 x) (hact ▸ hle)
            have h1 := Finset.inf'_le (fun j => if boxPiece U j x = boxFn U x then
              pieceLeft U j x else 1) (Finset.mem_range.mpr (by omega : k + 1 < k + 2))
            rw [ite_eq_left hact']  at h1
            rw [ite_eq_left hact]
            refine h1.trans ?_
            unfold pieceLeft
            rw [ite_eq_right (not_lt.mpr hxk.le), ite_eq_right (not_lt.mpr hxj.le)]
            have : (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ (k + 1) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            linarith
        · rw [ite_eq_right hact]
          refine (Finset.inf'_le _ (Finset.mem_range.mpr (by omega : 0 < k + 2))).trans ?_
          split_ifs
          · exact pieceLeft_le_one U 0 x
          · exact le_rfl
  have hL : boxLeft T x = boxLeft T' x := by
    rw [hleft T hpre hdev, hleft T' hpre' hdev']
    refine Finset.inf'_congr hne rfl (fun j hj => ?_)
    obtain ⟨h1, h2, -⟩ := hpiece j (Finset.mem_range.mp hj)
    rw [h1, h2, hfn]
  -- the right derivative, when positive, is attained up to depth `k + 1`
  have hright : ∀ U : Fin M → Bool, (∀ i : Fin M, (i : ℕ) < k → U i = pathBit x i) →
      U ⟨k, hk⟩ ≠ pathBit x k →
      let R := (Finset.range (k + 2)).sup' hne
        (fun j => if boxPiece U j x = boxFn U x then pieceRight U j x else -1)
      (0 < boxRight U x ↔ 0 < R) ∧ (0 < R → boxRight U x = R) := by
    intro U hU hU' R
    have hRle : R ≤ boxRight U x := Finset.sup'_mono _ hsub hne
    have hpos : 0 < boxRight U x → boxRight U x ≤ R := by
      intro h0
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        (fun j => if boxPiece U j x = boxFn U x then pieceRight U j x else -1)
      have hjM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hterm : 0 < (if boxPiece U j x = boxFn U x then pieceRight U j x else -1) := by
        rw [← hjeq]; exact h0
      by_cases hjk : j ≤ k + 1
      · unfold boxRight
        rw [hjeq]
        exact Finset.le_sup' (fun j => if boxPiece U j x = boxFn U x then pieceRight U j x
          else -1) (Finset.mem_range.mpr (by omega))
      · exfalso
        obtain ⟨-, hcase⟩ := deep_facts hk hU hU' j (by omega) hjM
        split_ifs at hterm with hact
        · rcases hcase with ⟨-, hlt⟩ | ⟨-, hxj, -⟩
          · have := piece_le_fn U hk2 x
            linarith
          · unfold pieceRight at hterm
            rw [ite_eq_left hxj] at hterm
            have : (0 : ℝ) < (1 / 2) ^ j := by positivity
            linarith
        · linarith
    refine ⟨⟨fun h0 => lt_of_lt_of_le h0 (hpos h0), fun h0 => lt_of_lt_of_le h0 hRle⟩,
      fun h0 => le_antisymm (hpos (lt_of_lt_of_le h0 hRle)) hRle⟩
  obtain ⟨hiff, heq⟩ := hright T hpre hdev
  obtain ⟨hiff', heq'⟩ := hright T' hpre' hdev'
  have hR : (Finset.range (k + 2)).sup' hne
      (fun j => if boxPiece T j x = boxFn T x then pieceRight T j x else -1) =
      (Finset.range (k + 2)).sup' hne
        (fun j => if boxPiece T' j x = boxFn T' x then pieceRight T' j x else -1) := by
    refine Finset.sup'_congr hne rfl (fun j hj => ?_)
    obtain ⟨h1, -, h3⟩ := hpiece j (Finset.mem_range.mp hj)
    rw [h1, h3, hfn]
  unfold boxOracle
  rw [hfn]
  congr 1
  by_cases h0 : 0 < boxRight T x
  · have h0' : 0 < boxRight T' x := hiff'.mpr (hR ▸ hiff.mp h0)
    rw [ite_eq_left h0, ite_eq_left h0', heq (hiff.mp h0), heq' (hiff'.mp h0'), hR]
  · have h0' : ¬ 0 < boxRight T' x := fun h => h0 (hiff.mpr (hR ▸ hiff'.mp h))
    rw [ite_eq_right h0, ite_eq_right h0', hL]

/-- The query of the emulation: the bits of the greedy path. -/
noncomputable def boxQuery (M : ℕ) (x : ℝ) : List (Fin M × Bool) :=
  (List.finRange M).map (fun i => (i, pathBit x i))

/-- The string completed from an answer of the string guessing oracle. -/
noncomputable def boxFill (M : ℕ) (x : ℝ) : Option ℕ → Fin M → Bool
  | none => fun i => pathBit x i
  | some k => fun i =>
      if (i : ℕ) < k then pathBit x i else if (i : ℕ) = k then !pathBit x i else false

/-- The answer of the emulation. -/
noncomputable def boxAnswer (M : ℕ) (x : ℝ) (ans : Option ℕ) : ℝ × ℝ :=
  boxOracle (boxFill M x ans) x

theorem query_none {S : Fin M → Bool} {x : ℝ} (h : stringGuess S (boxQuery M x) = none) :
    ∀ i, S i = pathBit x i := by
  unfold stringGuess boxQuery at h
  rw [List.findIdx?_eq_none_iff] at h
  intro i
  have := h (i, pathBit x i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  simpa using this

theorem query_some {S : Fin M → Bool} {x : ℝ} {k : ℕ}
    (h : stringGuess S (boxQuery M x) = some k) :
    ∃ hk : k < M, (∀ i : Fin M, (i : ℕ) < k → S i = pathBit x i) ∧ S ⟨k, hk⟩ ≠ pathBit x k := by
  unfold stringGuess boxQuery at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hlen, hp, hbefore⟩ := h
  simp only [List.length_map, List.length_finRange] at hlen
  refine ⟨hlen, fun i hi => ?_, ?_⟩
  · have := hbefore i hi
    simpa using this
  · simpa using hp

theorem box_emul (S : Fin M → Bool) (x : ℝ) :
    boxOracle S x = boxAnswer M x (stringGuess S (boxQuery M x)) := by
  cases hans : stringGuess S (boxQuery M x) with
  | none =>
    have := query_none hans
    unfold boxAnswer boxFill
    congr 1
    funext i
    exact this i
  | some k =>
    obtain ⟨hk, hpre, hdev⟩ := query_some hans
    unfold boxAnswer
    set F := boxFill M x (some k) with hF
    have hFpre : ∀ i : Fin M, (i : ℕ) < k → F i = pathBit x i := by
      intro i hi
      simp [hF, boxFill, hi]
    have hFdev : F ⟨k, hk⟩ ≠ pathBit x k := by
      simp [hF, boxFill]
    have hagree : ∀ i : Fin M, (i : ℕ) < k + 1 → S i = F i := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · rw [hpre i h, hFpre i h]
      · have hi' : i = ⟨k, hk⟩ := Fin.ext h
        subst hi'
        have hF' : F ⟨k, hk⟩ = !pathBit x k := by simp [hF, boxFill]
        rw [hF']
        cases hS : S ⟨k, hk⟩ <;> cases hp : pathBit x k <;> simp_all
    exact oracle_congr_of_deviate hk hpre hdev hFpre hFdev hagree

/-- Mapping the outputs of a query tree. -/
def mapOut {Q A X Y : Type} (g : X → Y) : QueryTree Q A X → QueryTree Q A Y
  | .ret x => .ret (g x)
  | .ask q next => .ask q (fun a => mapOut g (next a))

theorem mapOut_spec {Q A X Y : Type} (g : X → Y) (ans : Q → A) :
    ∀ t : QueryTree Q A X, (mapOut g t).output ans = g (t.output ans) ∧
      (mapOut g t).queries ans = t.queries ans := by
  intro t
  induction t with
  | ret x => exact ⟨rfl, rfl⟩
  | ask q next ih =>
    simp only [mapOut, QueryTree.output, QueryTree.queries]
    exact ⟨(ih _).1, by rw [(ih _).2]⟩

namespace Proof

theorem box_packing : BoxPacking := by
  intro M S
  refine ⟨box_min S, box_at_center S, fun S' ε x hε hS hS' => ?_⟩
  have h1 := path_of_near (near_of_opt hε hS)
  have h2 := path_of_near (near_of_opt hε hS')
  funext i
  rw [← h1 i, h2 i]

theorem box_emulation : BoxEmulation := fun M =>
  ⟨boxQuery M, boxAnswer M, fun S x => box_emul S x⟩

theorem box_lower_bound : BoxLowerBound := by
  classical
  intro M ε hε t Pe
  obtain ⟨t', ht'⟩ := Proof.emulation (fun S : Fin M → Bool => boxOracle S)
    (fun S : Fin M → Bool => stringGuess S) (boxQuery M) (boxAnswer M)
    (fun S x => box_emul S x) t
  set t'' := mapOut (fun x : ℝ => fun i : Fin M => pathBit x i) t' with ht''
  have hsg := (Proof.string_guessing M t'').2
  have hq : ∀ S : Fin M → Bool, t''.queries (stringGuess S) = t.queries (boxOracle S) := by
    intro S
    rw [ht'', (mapOut_spec _ _ t').2, (ht' S).2]
  have hout : ∀ S : Fin M → Bool,
      t''.output (stringGuess S) = fun i : Fin M => pathBit (t.output (boxOracle S)) i := by
    intro S
    rw [ht'', (mapOut_spec _ _ t').1, (ht' S).1]
  simp only [hq] at hsg
  -- the decoding errs only where the output is not `ε`-optimal
  have hsub : ∀ inst : DecidablePred (fun S : Fin M → Bool => t''.output (stringGuess S) ≠ S),
      ((@Finset.filter _ _ inst Finset.univ).card : ℝ) ≤
        ((Finset.univ.filter (fun S : Fin M → Bool =>
          ¬ ∀ y, boxFn S (t.output (boxOracle S)) ≤ boxFn S y + ε)).card : ℝ) := by
    intro inst
    have : @Finset.filter _ _ inst Finset.univ ⊆ Finset.univ.filter (fun S : Fin M → Bool =>
        ¬ ∀ y, boxFn S (t.output (boxOracle S)) ≤ boxFn S y + ε) := by
      intro S hS
      rw [Finset.mem_filter] at hS ⊢
      refine ⟨Finset.mem_univ S, fun hopt => hS.2 ?_⟩
      rw [hout S]
      funext i
      exact path_of_near (near_of_opt hε hopt) i
    exact_mod_cast Finset.card_le_card this
  have hpos : (0 : ℝ) < 2 ^ M := by positivity
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine le_trans ?_ hsg
  have key : ∀ c : ℝ, c ≤ ((Finset.univ.filter (fun S : Fin M → Bool =>
      ¬ ∀ y, boxFn S (t.output (boxOracle S)) ≤ boxFn S y + ε)).card : ℝ) →
      ((1 - Pe) * M - 1) / 2 ≤ ((1 - c / 2 ^ M) * M - 1) / 2 := by
    intro c hc
    have h1 : c / 2 ^ M ≤ Pe := by
      simp only [Pe]
      exact div_le_div_of_nonneg_right hc hpos.le
    have := mul_le_mul_of_nonneg_right h1 hM
    linarith
  exact key _ (hsub _)

end Proof

end Lemmata.OracleComplexity
