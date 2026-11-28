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

theorem piece_le_fn (S : Fin M → Bool) {j : ℕ} (hj : j ≤ M) (y : ℝ) :
    boxPiece S j y ≤ boxFn S y :=
  Finset.le_sup' (fun j => boxPiece S j y) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

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

/-- Beyond the first deviation, the oracle answer is fixed by the first `k + 1` bits. -/
theorem boxOracle_of_deviate {T : Fin M → Bool} {x : ℝ} {k : ℕ} (hk : k < M)
    (hpre : ∀ i : Fin M, (i : ℕ) < k → T i = pathBit x i) (hdev : T ⟨k, hk⟩ ≠ pathBit x k) :
    boxOracle T x = boxBest T x (k + 1) := by
  have hout := outside_of_deviate hk hpre hdev
  have hst := boxBest_stable T x (k := k + 1) (fun l hl hlM => by
    obtain ⟨h1, -⟩ := piece_chain T hout (l - (k + 1)) (by omega)
    rw [show k + 1 + (l - (k + 1)) = l by omega] at h1
    exact h1.trans (boxBest_ge T x (k + 1) le_rfl)) (M - (k + 1)) (by omega)
  rw [show k + 1 + (M - (k + 1)) = M by omega] at hst
  exact hst

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
    rw [boxOracle_of_deviate hk hpre hdev, boxOracle_of_deviate hk hFpre hFdev,
      boxBest_congr hagree x (k + 1) le_rfl]

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
