module

public import Lemmata.OracleComplexity.CubeBound

@[expose] public section

/-!
# The large-scale case for `ℓ^p` balls (Section V.A)

The hard function of signs `s ∈ {±1}^M` is `f_s(x) = max_{i<M} s_i x_i`. Its minimum over the unit
`ℓ^p` ball is at most `-M^{-1/p}`, attained at `x⋆ = -M^{-1/p} s`, so for `M ε^p < 1` every
`ε`-minimizer over the ball has `s_i x_i < 0` for all `i` and its signs recover `s`. The query
guesses, in the order of decreasing `|x_i|` (then increasing `i`), the signs that make each term
equal to `-|x_i|`; the first wrong guess at `j` gives the value `|x_j|`, and the least coordinate
attaining it and its sign are determined by the answer. An active coordinate is the one whose move
in the direction of its sign raises the value at rate `1`, so the oracle is local.
-/

namespace Lemmata.OracleComplexity

variable {n M : ℕ} [NeZero M]

theorem lp_term_le (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) (i : Fin M) :
    bitSign (s i) * x (Fin.castLE h i) ≤ lpFn h s x :=
  Finset.le_sup' (fun i : Fin M => bitSign (s i) * x (Fin.castLE h i)) (Finset.mem_univ i)

open Classical in
theorem lpCoord_spec (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) :
    bitSign (s (lpCoord h s x)) * x (Fin.castLE h (lpCoord h s x)) = lpFn h s x ∧
      ∀ i, bitSign (s i) * x (Fin.castLE h i) = lpFn h s x → lpCoord h s x ≤ i := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := Finset.min'_mem (Finset.univ.filter
      (fun i => bitSign (s i) * x (Fin.castLE h i) = lpFn h s x)) (by
        obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun i : Fin M => bitSign (s i) * x (Fin.castLE h i))
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm⟩⟩)
    exact (Finset.mem_filter.mp this).2
  · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> simp [bitSign]

theorem bitSign_mul_le_abs (b : Bool) (a : ℝ) : bitSign b * a ≤ |a| := by
  cases b <;> simp [bitSign, le_abs_self, neg_le_abs]

/-- One coordinate difference is at most the `ℓ^p` distance. -/
theorem coord_le_lp {p : ℝ} (hp : 1 ≤ p) (x y : Fin n → ℝ) (j : Fin n) :
    |x j - y j| ≤ (∑ i, |x i - y i| ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h1 : |x j - y j| ^ p ≤ ∑ i, |x i - y i| ^ p :=
    Finset.single_le_sum (f := fun i => |x i - y i| ^ p)
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ j)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1 (by positivity : 0 ≤ 1 / p)
  rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one] at h2

namespace Proof

theorem lp_oracle_valid : LpOracleValid := by
  intro n M _ h p hp s
  refine ⟨?_, fun x y => ?_, fun x => ⟨rfl, fun y => ?_⟩⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain ⟨i, -, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin M => bitSign (s i) * (a • x + b • y) (Fin.castLE h i))
    have k1 := mul_le_mul_of_nonneg_left (lp_term_le h s x i) ha
    have k2 := mul_le_mul_of_nonneg_left (lp_term_le h s y i) hb
    show lpFn h s (a • x + b • y) ≤ a • lpFn h s x + b • lpFn h s y
    have hval : lpFn h s (a • x + b • y) =
        a * (bitSign (s i) * x (Fin.castLE h i)) + b * (bitSign (s i) * y (Fin.castLE h i)) := by
      unfold lpFn
      rw [hmax]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hval]
    simp only [smul_eq_mul]
    linarith
  · have key : ∀ u v : Fin n → ℝ, lpFn h s u ≤ lpFn h s v + (∑ i, |u i - v i| ^ p) ^ (1 / p) := by
      intro u v
      apply Finset.sup'_le
      intro i _
      have h1 := coord_le_lp hp u v (Fin.castLE h i)
      have h2 := lp_term_le h s v i
      have h3 : bitSign (s i) * u (Fin.castLE h i) - bitSign (s i) * v (Fin.castLE h i) ≤
          |u (Fin.castLE h i) - v (Fin.castLE h i)| := by
        rw [← mul_sub]; exact bitSign_mul_le_abs _ _
      linarith
    have h1 := key x y
    have h2 := key y x
    have hsym : ∑ i, |y i - x i| ^ p = ∑ i, |x i - y i| ^ p := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [abs_sub_comm]
    rw [hsym] at h2
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨hc, -⟩ := lpCoord_spec h s x
    have h2 := lp_term_le h s y (lpCoord h s x)
    show lpFn h s x + bitSign (s (lpCoord h s x)) *
      (y (Fin.castLE h (lpCoord h s x)) - x (Fin.castLE h (lpCoord h s x))) ≤ lpFn h s y
    rw [← hc]
    linarith

end Proof

/-- `ε < M^{-1/p}` from `M ε^p < 1`. -/
theorem eps_lt_of_lp {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hM : (M : ℝ) * ε ^ p < 1) :
    ε < (M : ℝ) ^ (-1 / p) := by
  have hp0 : 0 < p := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : ε ^ p < (M : ℝ)⁻¹ := by
    rw [← one_div, lt_div_iff₀ hM0]; linarith [mul_comm (ε ^ p) (M : ℝ)]
  have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg hε.le _) h1 (by positivity : 0 < 1 / p)
  rw [← Real.rpow_mul hε.le, mul_one_div_cancel hp0.ne', Real.rpow_one, Real.inv_rpow hM0.le,
    ← Real.rpow_neg hM0.le] at h2
  rwa [show -(1 / p) = -1 / p by ring] at h2

/-- The comparison point `x⋆ = -M^{-1/p} s` on the first `M` coordinates. -/
noncomputable def lpStar (n : ℕ) (p : ℝ) (s : Fin M → Bool) : Fin n → ℝ :=
  fun j => if hj : (j : ℕ) < M then -bitSign (s ⟨j, hj⟩) * (M : ℝ) ^ (-1 / p) else 0

theorem lpStar_mem (h : M ≤ n) {p : ℝ} (hp : 1 ≤ p) (s : Fin M → Bool) :
    lpStar n p s ∈ lpBall p n := by
  have hp0 : 0 < p := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hc : ((M : ℝ) ^ (-1 / p)) ^ p = (M : ℝ)⁻¹ := by
    rw [← Real.rpow_mul hM0.le, show -1 / p * p = -1 by field_simp, Real.rpow_neg_one]
  have hterm : ∀ j : Fin n, |lpStar n p s j| ^ p =
      if (j : ℕ) < M then (M : ℝ)⁻¹ else 0 := by
    intro j
    unfold lpStar
    split_ifs with hj
    · rw [abs_mul, abs_neg, bitSign_abs, one_mul, abs_of_pos (by positivity), hc]
    · rw [abs_zero, Real.zero_rpow hp0.ne']
  show ∑ j, |lpStar n p s j| ^ p ≤ 1
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < M)).card = M := by
    rw [show Finset.univ.filter (fun j : Fin n => (j : ℕ) < M) =
      Finset.univ.map (Fin.castLEEmb h) by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Fin.castLEEmb_apply]
        constructor
        · intro hj; exact ⟨⟨j, hj⟩, Fin.ext rfl⟩
        · rintro ⟨i, -, rfl⟩; exact i.2]
    simp
  rw [hcard]
  field_simp
  rfl

theorem lpFn_star (h : M ≤ n) (p : ℝ) (s : Fin M → Bool) :
    lpFn h s (lpStar n p s) = -(M : ℝ) ^ (-1 / p) := by
  unfold lpFn
  have : ∀ i : Fin M, bitSign (s i) * lpStar n p s (Fin.castLE h i) = -(M : ℝ) ^ (-1 / p) := by
    intro i
    simp only [lpStar, Fin.val_castLE, Fin.is_lt, dite_true, Fin.eta]
    rw [show bitSign (s i) * (-bitSign (s i) * (M : ℝ) ^ (-1 / p)) =
      -(bitSign (s i) * bitSign (s i)) * (M : ℝ) ^ (-1 / p) by ring, bitSign_mul_self]
    ring
  rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun i _ => this i)]
  exact Finset.sup'_const _ _

/-- The signs of an `ε`-minimizer over the ball recover `s`. -/
theorem lp_decode (h : M ≤ n) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hM : (M : ℝ) * ε ^ p < 1)
    {s : Fin M → Bool} {x : Fin n → ℝ}
    (hopt : ∀ y ∈ lpBall p n, lpFn h s x ≤ lpFn h s y + ε) :
    ∀ i, decide (x (Fin.castLE h i) < 0) = s i := by
  intro i
  have h1 := hopt (lpStar n p s) (lpStar_mem h hp s)
  rw [lpFn_star] at h1
  have h2 := lp_term_le h s x i
  have h3 := eps_lt_of_lp hp hε hM
  have hneg : bitSign (s i) * x (Fin.castLE h i) < 0 := by linarith
  cases hs : s i
  · rw [hs] at hneg
    simp only [bitSign, Bool.false_eq_true, ite_false] at hneg
    simp only [decide_eq_false_iff_not, not_lt]
    linarith
  · rw [hs] at hneg
    simp only [bitSign, ite_true, one_mul] at hneg
    simpa using hneg

namespace Proof

theorem lp_packing : LpPacking := by
  intro n M _ h p ε hp hε hM s s' x _ hs hs'
  funext i
  rw [← lp_decode h hp hε hM hs i, lp_decode h hp hε hM hs' i]

end Proof

/-! ### Emulation by the string guessing oracle -/

/-- The order of the query: larger `|x_i|` first, then smaller `i`. -/
noncomputable def lpKey (h : M ≤ n) (x : Fin n → ℝ) (i : Fin M) : Lex (ℝᵒᵈ × Fin M) :=
  toLex (OrderDual.toDual |x (Fin.castLE h i)|, i)

omit [NeZero M] in
theorem lpKey_inj (h : M ≤ n) (x : Fin n → ℝ) {i j : Fin M} (he : lpKey h x i = lpKey h x j) :
    i = j := by
  unfold lpKey at he
  have := congrArg (fun p => (ofLex p).2) he
  simpa using this

omit [NeZero M] in
theorem lpKey_lt_iff (h : M ≤ n) (x : Fin n → ℝ) (i j : Fin M) :
    lpKey h x i < lpKey h x j ↔ |x (Fin.castLE h j)| < |x (Fin.castLE h i)| ∨
      (|x (Fin.castLE h i)| = |x (Fin.castLE h j)| ∧ i < j) := by
  unfold lpKey
  rw [Prod.Lex.toLex_lt_toLex]
  simp only [OrderDual.toDual_lt_toDual, OrderDual.toDual_inj]

/-- The guessed sign: the one that makes the term of the coordinate equal to `-|x_i|`. -/
noncomputable def lpGuess (h : M ≤ n) (x : Fin n → ℝ) (i : Fin M) : Bool :=
  decide (x (Fin.castLE h i) ≤ 0)

omit [NeZero M] in
theorem guess_term (h : M ≤ n) (x : Fin n → ℝ) (i : Fin M) :
    bitSign (lpGuess h x i) * x (Fin.castLE h i) = -|x (Fin.castLE h i)| := by
  unfold lpGuess bitSign
  by_cases hx : x (Fin.castLE h i) ≤ 0
  · simp [hx, abs_of_nonpos hx]
  · push Not at hx
    simp [not_le.mpr hx, abs_of_pos hx]

omit [NeZero M] in
theorem flip_term (h : M ≤ n) (x : Fin n → ℝ) (i : Fin M) :
    bitSign (!lpGuess h x i) * x (Fin.castLE h i) = |x (Fin.castLE h i)| := by
  unfold lpGuess bitSign
  by_cases hx : x (Fin.castLE h i) ≤ 0
  · simp [hx, abs_of_nonpos hx]
  · push Not at hx
    simp [not_le.mpr hx, abs_of_pos hx]

open Classical in
/-- The coordinates in the order of the query. -/
noncomputable def lpLabels (h : M ≤ n) (x : Fin n → ℝ) : List (Fin M) :=
  List.mergeSort (List.finRange M) (fun a b => decide (lpKey h x a ≤ lpKey h x b))

/-- The query: guess the signs that make all terms nonpositive, in the order of `lpKey`. -/
noncomputable def lpQuery (h : M ≤ n) (x : Fin n → ℝ) : List (Fin M × Bool) :=
  (lpLabels h x).map (fun i => (i, lpGuess h x i))

/-- The answer of the emulation: complete the string by the guesses, with the first wrong guess
flipped. -/
noncomputable def lpAnswer (h : M ≤ n) (x : Fin n → ℝ) : Option ℕ → ℝ × Fin n × ℝ
  | none => lpOracle h (lpGuess h x) x
  | some m => if hm : m < (lpLabels h x).length then
      lpOracle h (Function.update (lpGuess h x) (lpLabels h x)[m]
        (!lpGuess h x (lpLabels h x)[m])) x
    else lpOracle h (lpGuess h x) x

omit [NeZero M] in
theorem mem_lpLabels (h : M ≤ n) (x : Fin n → ℝ) (i : Fin M) : i ∈ lpLabels h x := by
  unfold lpLabels
  rw [List.mem_mergeSort]
  exact List.mem_finRange _

omit [NeZero M] in
open Classical in
theorem lpLabels_sorted (h : M ≤ n) (x : Fin n → ℝ) :
    (lpLabels h x).Pairwise (fun a b => decide (lpKey h x a ≤ lpKey h x b) = true) := by
  unfold lpLabels
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · intro a b
    rcases le_total (lpKey h x a) (lpKey h x b) with hh | hh <;> simp [hh]

/-- After a first wrong guess at `j`, the oracle answer does not depend on the signs of the
coordinates after `j` in the order of the query. -/
theorem lp_congr (h : M ≤ n) {s : Fin M → Bool} {x : Fin n → ℝ} (j : Fin M)
    (hbef : ∀ i, lpKey h x i < lpKey h x j → s i = lpGuess h x i)
    (hj : s j = !lpGuess h x j) :
    lpOracle h s x = lpOracle h (Function.update (lpGuess h x) j (!lpGuess h x j)) x := by
  set T := Function.update (lpGuess h x) j (!lpGuess h x j) with hT
  have hTj : T j = !lpGuess h x j := by simp [hT]
  have hTi : ∀ i, i ≠ j → T i = lpGuess h x i := fun i hi => by simp [hT, hi]
  have hsj : bitSign (s j) * x (Fin.castLE h j) = |x (Fin.castLE h j)| := by
    rw [hj]; exact flip_term h x j
  have hTj' : bitSign (T j) * x (Fin.castLE h j) = |x (Fin.castLE h j)| := by
    rw [hTj]; exact flip_term h x j
  have tri : ∀ i, i ≠ j → lpKey h x i < lpKey h x j ∨ lpKey h x j < lpKey h x i :=
    fun i hi => lt_or_gt_of_ne (fun he => hi (lpKey_inj h x he))
  have later : ∀ i, lpKey h x j < lpKey h x i →
      |x (Fin.castLE h i)| ≤ |x (Fin.castLE h j)| ∧
        (|x (Fin.castLE h i)| = |x (Fin.castLE h j)| → j < i) := by
    intro i hi
    rw [lpKey_lt_iff] at hi
    rcases hi with hi | ⟨he, hlt⟩
    · exact ⟨hi.le, fun he => absurd he hi.ne⟩
    · exact ⟨he.ge, fun _ => hlt⟩
  have ne_of_key : ∀ i, lpKey h x i < lpKey h x j → i ≠ j :=
    fun i hk he => lt_irrefl _ (he ▸ hk)
  have hj0 := abs_nonneg (x (Fin.castLE h j))
  -- the values
  have hfs : lpFn h s x = |x (Fin.castLE h j)| := by
    refine le_antisymm (Finset.sup'_le _ _ (fun i _ => ?_)) (hsj ▸ lp_term_le h s x j)
    by_cases he : i = j
    · rw [he, hsj]
    · rcases tri i he with hk | hk
      · rw [hbef i hk, guess_term]
        linarith [abs_nonneg (x (Fin.castLE h i))]
      · exact (bitSign_mul_le_abs _ _).trans (later i hk).1
  have hfT : lpFn h T x = |x (Fin.castLE h j)| := by
    refine le_antisymm (Finset.sup'_le _ _ (fun i _ => ?_)) (hTj' ▸ lp_term_le h T x j)
    by_cases he : i = j
    · rw [he, hTj']
    · rw [hTi i he, guess_term]
      linarith [abs_nonneg (x (Fin.castLE h i))]
  -- the least active coordinates
  have hcs := lpCoord_spec h s x
  have hcT := lpCoord_spec h T x
  have hcs_le : lpCoord h s x ≤ j := hcs.2 j (by rw [hsj, hfs])
  have hcT_le : lpCoord h T x ≤ j := hcT.2 j (by rw [hTj', hfT])
  have hcase : lpCoord h s x = j ∨ lpKey h x (lpCoord h s x) < lpKey h x j := by
    by_cases he : lpCoord h s x = j
    · exact Or.inl he
    · right
      have hlt : lpCoord h s x < j := lt_of_le_of_ne hcs_le he
      rcases tri _ he with hk | hk
      · exact hk
      · exfalso
        have hact := hcs.1
        rw [hfs] at hact
        have h1 := bitSign_mul_le_abs (s (lpCoord h s x)) (x (Fin.castLE h (lpCoord h s x)))
        have h2 := (later _ hk).1
        have heq : |x (Fin.castLE h (lpCoord h s x))| = |x (Fin.castLE h j)| := by linarith
        exact absurd ((later _ hk).2 heq) (not_lt.mpr hlt.le)
  have h1 : bitSign (T (lpCoord h s x)) * x (Fin.castLE h (lpCoord h s x)) = lpFn h T x := by
    rcases hcase with he | hk
    · rw [he, hTj', hfT]
    · have hact := hcs.1
      rw [hbef _ hk, guess_term, hfs] at hact
      rw [hTi _ (ne_of_key _ hk), guess_term, hfT]
      exact hact
  have h2 : bitSign (s (lpCoord h T x)) * x (Fin.castLE h (lpCoord h T x)) = lpFn h s x := by
    by_cases he : lpCoord h T x = j
    · rw [he, hsj, hfs]
    · have hlt : lpCoord h T x < j := lt_of_le_of_ne hcT_le he
      have hact := hcT.1
      rw [hTi _ he, guess_term, hfT] at hact
      rcases tri _ he with hk | hk
      · rw [hbef _ hk, guess_term, hfs]
        exact hact
      · exfalso
        have h0 : |x (Fin.castLE h (lpCoord h T x))| = |x (Fin.castLE h j)| := by
          linarith [abs_nonneg (x (Fin.castLE h (lpCoord h T x)))]
        exact absurd ((later _ hk).2 h0) (not_lt.mpr hlt.le)
  have hc : lpCoord h s x = lpCoord h T x := le_antisymm (hcs.2 _ h2) (hcT.2 _ h1)
  have hbit : s (lpCoord h s x) = T (lpCoord h s x) := by
    rcases hcase with he | hk
    · rw [he, hj, hTj]
    · rw [hbef _ hk, hTi _ (ne_of_key _ hk)]
  show (lpFn h s x, Fin.castLE h (lpCoord h s x), bitSign (s (lpCoord h s x))) =
    (lpFn h T x, Fin.castLE h (lpCoord h T x), bitSign (T (lpCoord h T x)))
  rw [hfs, hfT, hbit, hc]

theorem lp_emul (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) :
    lpOracle h s x = lpAnswer h x (stringGuess s (lpQuery h x)) := by
  classical
  have hmatch_iff : ∀ i, (s i != lpGuess h x i) = false ↔ s i = lpGuess h x i := by
    intro i
    cases s i <;> cases lpGuess h x i <;> simp
  cases hans : stringGuess s (lpQuery h x) with
  | none =>
    unfold stringGuess lpQuery at hans
    rw [List.findIdx?_eq_none_iff] at hans
    have hs : s = lpGuess h x := by
      funext i
      have := hans (i, lpGuess h x i) (List.mem_map.mpr ⟨i, mem_lpLabels h x i, rfl⟩)
      exact (hmatch_iff i).mp this
    rw [hs]
    simp only [lpAnswer]
  | some m =>
    unfold stringGuess lpQuery at hans
    rw [List.findIdx?_eq_some_iff_getElem] at hans
    obtain ⟨hm, hmis, hbefore⟩ := hans
    simp only [List.length_map] at hm
    set L := lpLabels h x with hL
    set j := L[m] with hjdef
    have hmis' : s j = !lpGuess h x j := by
      have hne : s j ≠ lpGuess h x j := by
        intro he
        have := (hmatch_iff j).mpr he
        simp only [List.getElem_map] at hmis
        rw [this] at hmis
        exact Bool.false_ne_true hmis
      cases hs : s j <;> cases hg : lpGuess h x j <;> simp_all
    have hbef : ∀ i, lpKey h x i < lpKey h x j → s i = lpGuess h x i := by
      intro i hi
      obtain ⟨q, hq, hqi⟩ := List.mem_iff_getElem.mp (mem_lpLabels h x i)
      rcases lt_trichotomy q m with hqm | hqm | hqm
      · have := hbefore q hqm
        simp only [List.getElem_map, hqi] at this
        exact (hmatch_iff i).mp (by simpa using this)
      · exfalso
        subst hqm
        have hij : i = j := hqi.symm.trans rfl
        rw [hij] at hi
        exact lt_irrefl _ hi
      · exfalso
        have hsorted := List.pairwise_iff_getElem.mp (lpLabels_sorted h x) m q hm hq hqm
        simp only [decide_eq_true_eq] at hsorted
        rw [hqi] at hsorted
        exact absurd hi (not_lt.mpr (hsorted : lpKey h x j ≤ lpKey h x i))
    rw [lp_congr h j hbef hmis']
    show _ = lpAnswer h x (some m)
    simp only [lpAnswer]
    rw [dite_eq_left hm]

/-! ### Locality -/

omit [NeZero M] in
theorem lp_update_other (h : M ≤ n) (x : Fin n → ℝ) (k i : Fin M) (hik : i ≠ k) (z : ℝ) :
    Function.update x (Fin.castLE h k) z (Fin.castLE h i) = x (Fin.castLE h i) := by
  rw [Function.update_of_ne]
  intro he
  exact hik (Fin.castLE_injective h he)

theorem lp_active_moves (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) (k : Fin M)
    (hk : bitSign (s k) * x (Fin.castLE h k) = lpFn h s x) (t : ℝ) :
    lpFn h s x + t ≤ lpFn h s (Function.update x (Fin.castLE h k)
      (x (Fin.castLE h k) + bitSign (s k) * t)) := by
  have := lp_term_le h s (Function.update x (Fin.castLE h k)
    (x (Fin.castLE h k) + bitSign (s k) * t)) k
  rw [Function.update_self] at this
  have hsq := bitSign_mul_self (s k)
  have : bitSign (s k) * (x (Fin.castLE h k) + bitSign (s k) * t) = lpFn h s x + t := by
    rw [mul_add, ← mul_assoc, hsq, one_mul, hk]
  linarith

theorem lp_active_back (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) (k : Fin M)
    (hk : bitSign (s k) * x (Fin.castLE h k) = lpFn h s x) {t : ℝ} (ht : 0 ≤ t) :
    lpFn h s (Function.update x (Fin.castLE h k)
      (x (Fin.castLE h k) - bitSign (s k) * t)) ≤ lpFn h s x := by
  apply Finset.sup'_le
  intro i _
  by_cases hik : i = k
  · subst hik
    rw [Function.update_self, mul_sub, ← mul_assoc, bitSign_mul_self, one_mul, hk]
    linarith
  · rw [lp_update_other h x k i hik]
    exact lp_term_le h s x i

theorem lp_inactive_still (h : M ≤ n) (s : Fin M → Bool) (x : Fin n → ℝ) (k : Fin M)
    (hk : bitSign (s k) * x (Fin.castLE h k) ≠ lpFn h s x) :
    ∃ δ > 0, ∀ t, |t| < δ →
      lpFn h s (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t)) = lpFn h s x := by
  have hlt : bitSign (s k) * x (Fin.castLE h k) < lpFn h s x :=
    lt_of_le_of_ne (lp_term_le h s x k) hk
  refine ⟨lpFn h s x - bitSign (s k) * x (Fin.castLE h k), by linarith, fun t ht => ?_⟩
  obtain ⟨hc, -⟩ := lpCoord_spec h s x
  have hck : lpCoord h s x ≠ k := by
    intro he
    rw [he] at hc
    exact hk hc
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    by_cases hik : i = k
    · subst hik
      rw [Function.update_self, mul_add]
      have := bitSign_mul_le_abs (s i) t
      have := le_abs_self t
      linarith
    · rw [lp_update_other h x k i hik]
      exact lp_term_le h s x i
  · have := lp_term_le h s (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t))
      (lpCoord h s x)
    rw [lp_update_other h x k _ hck, hc] at this
    exact this

namespace Proof

theorem lp_local : LpLocal := by
  intro n M _ h s s' x hev
  obtain ⟨ε, hε, hU⟩ := Metric.eventually_nhds_iff.mp hev
  have hU' : ∀ k : Fin M, ∀ t, |t| < ε →
      lpFn h s (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t)) =
        lpFn h s' (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t)) :=
    fun k t ht => hU (by rw [dist_update]; exact ht)
  have hx : lpFn h s x = lpFn h s' x := hU (by simpa using hε)
  -- the same coordinates attain the maximum
  have hact : ∀ (T T' : Fin M → Bool),
      (∀ k : Fin M, ∀ t, |t| < ε →
        lpFn h T (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t)) =
          lpFn h T' (Function.update x (Fin.castLE h k) (x (Fin.castLE h k) + t))) →
      lpFn h T x = lpFn h T' x →
      ∀ k, bitSign (T k) * x (Fin.castLE h k) = lpFn h T x →
        bitSign (T' k) * x (Fin.castLE h k) = lpFn h T' x := by
    intro T T' hTT hTx k hk
    by_contra hk'
    obtain ⟨δ, hδ, hstill⟩ := lp_inactive_still h T' x k hk'
    set t := min δ ε / 2 with htdef
    have ht : 0 < t := by positivity
    have htδ : t < δ := by have := min_le_left δ ε; linarith
    have htε : t < ε := by have := min_le_right δ ε; linarith
    have habs : |bitSign (T k) * t| = t := by rw [abs_mul, bitSign_abs, one_mul, abs_of_pos ht]
    have e1 := lp_active_moves h T x k hk t
    rw [hTT k _ (by rw [habs]; exact htε), hstill _ (by rw [habs]; exact htδ), ← hTx] at e1
    linarith
  have hiff : ∀ k, bitSign (s k) * x (Fin.castLE h k) = lpFn h s x ↔
      bitSign (s' k) * x (Fin.castLE h k) = lpFn h s' x :=
    fun k => ⟨hact s s' hU' hx k, hact s' s (fun k t ht => (hU' k t ht).symm) hx.symm k⟩
  have hc : lpCoord h s x = lpCoord h s' x := by
    obtain ⟨h1, h2⟩ := lpCoord_spec h s x
    obtain ⟨h1', h2'⟩ := lpCoord_spec h s' x
    exact le_antisymm (h2 _ ((hiff _).mpr h1')) (h2' _ ((hiff _).mp h1))
  set c := lpCoord h s x with hcdef
  have hcs : bitSign (s c) * x (Fin.castLE h c) = lpFn h s x := (lpCoord_spec h s x).1
  have hcs' : bitSign (s' c) * x (Fin.castLE h c) = lpFn h s' x := (hiff c).mp hcs
  -- the same sign: the value rises along `s_c e_c` and does not rise along `-s'_c e_c`
  have hbit : s c = s' c := by
    by_contra hne
    have hflip : bitSign (s' c) = -bitSign (s c) := by
      cases hs : s c <;> cases hs' : s' c <;> simp_all [bitSign]
    set t := ε / 2 with htdef
    have ht : 0 < t := by positivity
    have habs : |bitSign (s c) * t| < ε := by
      rw [abs_mul, bitSign_abs, one_mul, abs_of_pos ht]; linarith
    have e1 := lp_active_moves h s x c hcs t
    have e2 := lp_active_back h s' x c hcs' ht.le
    rw [hflip, sub_eq_add_neg, ← neg_mul, neg_neg] at e2
    rw [hU' c _ habs] at e1
    linarith
  show (lpFn h s x, Fin.castLE h (lpCoord h s x), bitSign (s (lpCoord h s x))) =
    (lpFn h s' x, Fin.castLE h (lpCoord h s' x), bitSign (s' (lpCoord h s' x)))
  rw [hx, ← hc, hbit]

theorem lp_emulation : LpEmulation := fun _ _ _ h =>
  ⟨lpQuery h, lpAnswer h, fun s x => lp_emul h s x⟩

theorem lp_lower_bound : LpLowerBound := by
  classical
  intro n M _ h p ε hp hε hM t Pe
  obtain ⟨t', ht'⟩ := Proof.emulation (fun s : Fin M → Bool => lpOracle h s)
    (fun s : Fin M → Bool => stringGuess s) (lpQuery h) (lpAnswer h)
    (fun s x => lp_emul h s x) t
  set dec : (Fin n → ℝ) → Fin M → Bool := fun y i => decide (y (Fin.castLE h i) < 0) with hdec
  set t'' := mapOut dec t' with ht''
  have hsg := (Proof.string_guessing M t'').2
  have hq : ∀ s : Fin M → Bool, t''.queries (stringGuess s) = t.queries (lpOracle h s) := by
    intro s
    rw [ht'', (mapOut_spec _ _ t').2, (ht' s).2]
  have hout : ∀ s : Fin M → Bool,
      t''.output (stringGuess s) = dec (t.output (lpOracle h s)) := by
    intro s
    rw [ht'', (mapOut_spec _ _ t').1, (ht' s).1]
  have hsum : ∑ s : Fin M → Bool, (t''.queries (stringGuess s) : ℝ) =
      ∑ s : Fin M → Bool, (t.queries (lpOracle h s) : ℝ) :=
    Finset.sum_congr rfl (fun s _ => by rw [hq])
  have hcard : ∀ inst : DecidablePred (fun U : Fin M → Bool => t''.output (stringGuess U) ≠ U),
      ((@Finset.filter _ _ inst Finset.univ).card : ℝ) ≤
        ((Finset.univ.filter (fun s : Fin M → Bool =>
          ¬ (t.output (lpOracle h s) ∈ lpBall p n ∧ ∀ y ∈ lpBall p n,
            lpFn h s (t.output (lpOracle h s)) ≤ lpFn h s y + ε))).card : ℝ) := by
    intro inst
    have hsub : (@Finset.filter _ _ inst Finset.univ) ⊆ Finset.univ.filter
        (fun s : Fin M → Bool => ¬ (t.output (lpOracle h s) ∈ lpBall p n ∧ ∀ y ∈ lpBall p n,
          lpFn h s (t.output (lpOracle h s)) ≤ lpFn h s y + ε)) := by
      intro U hU
      rw [Finset.mem_filter] at hU ⊢
      refine ⟨Finset.mem_univ _, fun hopt => hU.2 ?_⟩
      rw [hout]
      funext i
      exact lp_decode h hp hε hM hopt.2 i
    exact_mod_cast Finset.card_le_card hsub
  have hpos : (0 : ℝ) < 2 ^ M := by positivity
  rw [hsum] at hsg
  have hM0 : (0 : ℝ) ≤ M := by positivity
  refine le_trans ?_ hsg
  have key : ∀ c : ℝ, c ≤ ((Finset.univ.filter (fun s : Fin M → Bool =>
      ¬ (t.output (lpOracle h s) ∈ lpBall p n ∧ ∀ y ∈ lpBall p n,
        lpFn h s (t.output (lpOracle h s)) ≤ lpFn h s y + ε))).card : ℝ) →
      ((1 - Pe) * M - 1) / 2 ≤ ((1 - c / 2 ^ M) * M - 1) / 2 := by
    intro c hc
    have h1 : c / 2 ^ M ≤ Pe := by
      simp only [Pe]
      exact div_le_div_of_nonneg_right hc hpos.le
    have := mul_le_mul_of_nonneg_right h1 hM0
    linarith
  exact key _ (hcard _)

end Proof

end Lemmata.OracleComplexity
