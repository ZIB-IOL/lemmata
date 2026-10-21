module

public import Lemmata.TensorRank.Proof.SymmetricSeparation
public import Lemmata.TensorRank.Proof.PolynomialProfile
public import Lemmata.TensorRank.Proof.ProfileDiagonal
public import Lemmata.TensorRank.Proof.GraphExponent
public import Lemmata.TensorRank.Proof.Refinement
public import Lemmata.TensorRank.Proof.Formats
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace Lemmata.TensorRank.TensorSemiring

variable {k : ℕ} [Nonempty (Fin k)] (f : Character k)
variable {I J : Type} [Fintype I] [Fintype J]

def onParties (e : Fin k ≃ I) {V : I → Type} [∀ i, Fintype (V i)]
    (T : Tensor ℂ I V) : ℝ := normalizedEval f (Tensor.relabel e T)

omit [Nonempty (Fin k)] [Fintype I] in
theorem onParties_equiv (e d : Fin k ≃ I)
    {V : I → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ I V) :
    onParties f e T = onParties f d T := by
  let σ : Equiv.Perm (Fin k) := d.trans e.symm
  have hσ : σ.trans e = d := by ext i; simp [σ]
  have h := symmetricEval_relabel f (meanExponent f) σ (Tensor.relabel e T)
  rw [Tensor.relabel_comp] at h
  change onParties f (σ.trans e) T = onParties f e T at h
  rw [hσ] at h
  exact h.symm

omit [Nonempty (Fin k)] [Fintype I] [Fintype J] in
theorem onParties_transport (e : Fin k ≃ I) (d : Fin k ≃ J) (g : J ≃ I)
    {V : I → Type} [∀ i, Fintype (V i)] (T : Tensor ℂ I V) :
    onParties f d (Tensor.relabel g T) = onParties f e T := by
  change normalizedEval f (Tensor.relabel d (Tensor.relabel g T)) = _
  rw [Tensor.relabel_comp]
  exact onParties_equiv f (d.trans g) e T

variable (e : Fin k ≃ I) {V W : I → Type}
variable [∀ i, Fintype (V i)] [∀ i, Fintype (W i)]

omit [Fintype I] in
theorem onParties_nonneg (T : Tensor ℂ I V) : 0 ≤ onParties f e T :=
  normalizedEval_nonneg f _

omit [Nonempty (Fin k)] [Fintype I] in
theorem onParties_reindex (c : ∀ i, W i ≃ V i) (T : Tensor ℂ I V) :
    onParties f e (Tensor.reindex (fun i => c i) T) = onParties f e T := by
  change symmetricEval f (meanExponent f) (Tensor.relabel e (Tensor.reindex _ T)) = _
  rw [Tensor.relabel_reindex, symmetricEval_reindex]
  rfl

omit [Fintype I] in
theorem onParties_product (S : Tensor ℂ I V) (T : Tensor ℂ I W) :
    onParties f e (Tensor.product S T) = onParties f e S * onParties f e T := by
  change symmetricEval f (meanExponent f) (Tensor.relabel e (Tensor.product S T)) = _
  rw [Tensor.relabel_product, symmetricEval_product]
  rfl

omit [Nonempty (Fin k)] [Fintype I] in
theorem onParties_relabel (σ : Equiv.Perm I) (T : Tensor ℂ I V) :
    onParties f e (Tensor.relabel σ T) = onParties f e T :=
  onParties_transport f e e σ T

theorem onParties_mono (hk : 2 ≤ k) {S : Tensor ℂ I W} {T : Tensor ℂ I V}
    (h : Tensor.Restricts S T) : onParties f e S ≤ onParties f e T :=
  symmetricEval_mono f _ (meanExponent_pos f hk) (h.relabel e)

theorem onParties_degenerates (hk : 2 ≤ k) {S : Tensor ℂ I W} {T : Tensor ℂ I V}
    (h : Tensor.Degenerates S T) : onParties f e S ≤ onParties f e T :=
  symmetricEval_degenerates f _ (meanExponent_pos f hk) (h.relabel e)

theorem onParties_le_rank (hk : 2 ≤ k) (T : Tensor ℂ I V) :
    onParties f e T ≤ (Tensor.rank T : ℝ) ^ (1 / meanExponent f) := by
  have h := normalizedEval_le_rank f hk (Tensor.relabel e T)
  rwa [Tensor.rank_relabel] at h

omit [Fintype I] in
theorem one_le_onParties (hk : 2 ≤ k) {T : Tensor ℂ I V} (hT : T ≠ 0) :
    1 ≤ onParties f e T := by
  apply one_le_normalizedEval f hk
  intro h
  apply hT
  funext x
  have hx := congrFun h ((Equiv.piCongrLeft V e).symm x)
  simpa only [Tensor.relabel, Equiv.apply_symm_apply, Pi.zero_apply] using hx

omit [Fintype I] [∀ i, Fintype (V i)] in
private theorem reads_of_eq {C : Type} {Z : C → Tensor ℂ I V} {i j : I}
    (h : i = j) {label : V j → C} (hz : Tensor.Reads Z j label) :
    Tensor.Reads Z i (fun x => label (cast (congrArg V h) x)) := by
  cases h
  exact hz

omit [Fintype I] in
theorem onParties_readable_sum (hk : 2 ≤ k) (a b : I) (hab : a ≠ b)
    {C : Type} [Fintype C] (Z : C → Tensor ℂ I V)
    {left : V a → C} {right : V b → C}
    (hl : Tensor.Reads Z a left) (hr : Tensor.Reads Z b right) :
    (∑ c, onParties f e (Z c)) ≤ onParties f e (∑ c, Z c) := by
  have hl' := Tensor.Reads.relabel e (e.symm a) (reads_of_eq (e.apply_symm_apply a) hl)
  have hr' := Tensor.Reads.relabel e (e.symm b) (reads_of_eq (e.apply_symm_apply b) hr)
  have h := normalizedEval_readable_sum f hk (e.symm a) (e.symm b)
    (fun h => hab (e.symm.injective h)) (fun c => Tensor.relabel e (Z c)) hl' hr'
  rw [← Tensor.relabel_sum] at h
  exact h

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem onParties_canonical_pairing (hk : 2 ≤ k) (a b : Fin k) (hab : a ≠ b)
    {M : ℕ} (hM : 1 ≤ M) :
    onParties f (Separation.readerEquiv a b hab).symm (Separation.readerPairing M) = M := by
  let g := Separation.readerEquiv a b hab
  let G := weightedComplete (singleEdgeDimensions (edgeBetween a b hab.symm) M)
  have hprod : symmetricProduct f (ofTensor (Tensor.relabel g.symm (Separation.readerPairing M))) =
      symmetricProduct f (ofTensor G) := by
    apply Finset.prod_congr rfl
    intro σ _
    exact Separation.character_readerPairing_eq (f.permute σ) a b hab M
  change symmetricProduct f (ofTensor (Tensor.relabel g.symm (Separation.readerPairing M))) ^
    (1 / ((Fintype.card (Equiv.Perm (Fin k)) : ℝ) * meanExponent f)) = M
  rw [hprod]
  exact normalizedEval_singleEdge f hk _ hM

private def pairingCoordinate {J : Type} {r : ℕ} (g : Fin r ≃ J) (p : Separation.Party r) :
    Separation.PairCoordinate 2 p ≃ PolynomialProduct.BitCoordinate
      (Equiv.sumCongr (Equiv.refl Bool) g p) := by
  rcases p with b | j
  · cases b <;> exact Equiv.refl _
  · exact Equiv.refl _

private theorem pairing_relabel {J : Type} {r : ℕ} (g : Fin r ≃ J) :
    Tensor.reindex (fun p => pairingCoordinate g p)
      (Tensor.relabel (Equiv.sumCongr (Equiv.refl Bool) g)
        (PolynomialProduct.pairing (J := J))) = Separation.readerPairing 2 := by
  funext x
  let e := Equiv.sumCongr (Equiv.refl Bool) g
  let y := Equiv.piCongrLeft PolynomialProduct.BitCoordinate e
    (fun p => pairingCoordinate g p (x p))
  have hy (b : Bool) : y (.inl b) = x (.inl b) := by
    change (Equiv.piCongrLeft PolynomialProduct.BitCoordinate e
      (fun p => pairingCoordinate g p (x p))) (e (.inl b)) = _
    rw [Equiv.piCongrLeft_apply_apply]
    cases b <;> rfl
  change (if y (.inl false) = y (.inl true) then (1 : ℂ) else 0) = _
  rw [hy false, hy true]
  rfl

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem onParties_pairing (hk : 2 ≤ k) (d : Fin k ≃ (Bool ⊕ J)) :
    onParties f d (PolynomialProduct.pairing (J := J)) = 2 := by
  have hc : Fintype.card J = k - 2 := by
    have h := Fintype.card_congr d
    simp only [Fintype.card_sum, Fintype.card_bool, Fintype.card_fin] at h
    omega
  let g := (Fintype.equivFinOfCardEq hc).symm
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  let c := (Separation.readerEquiv a b hab).symm
  have h := onParties_reindex f c (fun p => pairingCoordinate g p)
    (Tensor.relabel (Equiv.sumCongr (Equiv.refl Bool) g) (PolynomialProduct.pairing (J := J)))
  rw [pairing_relabel] at h
  rw [onParties_transport f d c _ _] at h
  rw [← h]
  exact onParties_canonical_pairing f hk a b hab (by decide)

omit [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (W i)] in
theorem onParties_laws (hk : 2 ≤ k) (d : Fin k ≃ (Bool ⊕ J)) :
    PolynomialProduct.Functional.Laws (fun {_} [_] => onParties f d) where
  restricts h := onParties_mono f d hk h
  degenerates h := onParties_degenerates f d hk h
  product S T := onParties_product f d S T
  relabel σ T := onParties_relabel f d σ T
  readerSum Z left right hl hr :=
    onParties_readable_sum f d hk (.inl false) (.inl true) (by simp) Z hl hr
  pairing := onParties_pairing f hk d

def polynomialProfile {m : ℕ} (e : Fin k ≃ Option (Fin m)) (a : Fin m → ℕ) : ℝ :=
  onParties f e (PolynomialProduct.tensor a)

private def selectedProfile {J : Type} [Fintype J] (e : Fin k ≃ (Bool ⊕ J))
    (a : J → ℕ) (b : ℕ) : ℝ := onParties f e (PolynomialProduct.selected a b)

private theorem remaining_update {K : Type} [DecidableEq K] (a : K → ℕ) (j : K) (b : ℕ) :
    PolynomialProduct.remaining (Function.update a j b) j = PolynomialProduct.remaining a j := by
  funext i
  exact Function.update_of_ne i.property _ _

private theorem remaining_degree {m : ℕ} (a : Fin m → ℕ) (j : Fin m) :
    PolynomialProduct.degree (PolynomialProduct.remaining a j) =
      ∑ i ∈ Finset.univ.erase j, (a i - 1) := by
  unfold PolynomialProduct.degree PolynomialProduct.remaining
  exact (Finset.sum_subtype (Finset.univ.erase j) (by simp) (fun i => a i - 1)).symm

omit [Nonempty (Fin k)] in
private theorem selected_value {K : Type} [Fintype K] (j : K)
    [finiteOther : Fintype (PolynomialProduct.Other j)]
    (d : Fin k ≃ (Bool ⊕ PolynomialProduct.Other j))
    (hF : PolynomialProduct.Functional.Laws (fun {_} [_] => onParties f d))
    (a : K → ℕ) (hj : 0 < a j) :
    selectedProfile f d (PolynomialProduct.remaining a j) (a j) =
      onParties f d (Tensor.relabel (PolynomialProduct.inputPartyEquiv j) (PolynomialProduct.tensor a)) := by
  let canonical : Fintype (PolynomialProduct.Other j) :=
    @Subtype.fintype K (fun i => i ≠ j)
      (fun i => @instDecidableNot (i = j) (Classical.propDecidable _)) inferInstance
  have hi : finiteOther = canonical := Subsingleton.elim _ _
  rw [hi] at hF ⊢
  exact PolynomialProduct.selected_value_relabel_tensor hF a hj

private theorem polynomialProfile_update {m : ℕ} (hk : 2 ≤ k)
    (e : Fin k ≃ Option (Fin m)) (a : Fin m → ℕ) (j : Fin m) (b : ℕ) (hb : 0 < b) :
    polynomialProfile f e (Function.update a j b) =
      onParties f (e.trans (PolynomialProduct.inputPartyEquiv j).symm)
        (PolynomialProduct.selected (PolynomialProduct.remaining a j) b) := by
  let d := e.trans (PolynomialProduct.inputPartyEquiv j).symm
  have h := selected_value f j d (onParties_laws f hk d)
    (Function.update a j b) (by simpa only [Function.update_self] using hb)
  rw [onParties_transport f e d _ _] at h
  change selectedProfile f d (PolynomialProduct.remaining (Function.update a j b) j)
    (Function.update a j b j) = polynomialProfile f e (Function.update a j b) at h
  rw [Function.update_self, remaining_update] at h
  exact h.symm

theorem polynomialProfile_nonnegative {m : ℕ} (e : Fin k ≃ Option (Fin m)) :
    Profile.Nonnegative (polynomialProfile f e) := by
  intro a _
  exact onParties_nonneg f e _

theorem polynomialProfile_concavity {m : ℕ} (hk : 2 ≤ k)
    (e : Fin k ≃ Option (Fin m)) : Profile.Concavity (polynomialProfile f e) := by
  intro a _ j b hb
  rw [polynomialProfile_update f hk e a j b (by omega),
    polynomialProfile_update f hk e a j (b + 2) (by omega),
    polynomialProfile_update f hk e a j (b + 1) (by omega)]
  have h := PolynomialProduct.selected_concavity
    (onParties_laws f hk (e.trans (PolynomialProduct.inputPartyEquiv j).symm))
    (PolynomialProduct.remaining a j) (b + 1) (by omega)
  change selectedProfile f _ _ (b + 1 - 1) + selectedProfile f _ _ (b + 1 + 1) ≤
    2 * selectedProfile f _ _ (b + 1) at h
  rw [show b + 1 - 1 = b by omega, show b + 1 + 1 = b + 2 by omega] at h
  exact h

theorem polynomialProfile_tripling {m : ℕ} (hk : 2 ≤ k)
    (e : Fin k ≃ Option (Fin m)) : Profile.Tripling (polynomialProfile f e) := by
  intro a _ j b hb
  rw [polynomialProfile_update f hk e a j b (by omega),
    polynomialProfile_update f hk e a j _ (by omega)]
  have h := PolynomialProduct.selected_tripling
    (onParties_laws f hk (e.trans (PolynomialProduct.inputPartyEquiv j).symm))
    (PolynomialProduct.remaining a j) b
  change 3 * selectedProfile f _ _ b ≤ selectedProfile f _ _
    (3 * b + PolynomialProduct.degree (PolynomialProduct.remaining a j)) at h
  rw [remaining_degree] at h
  exact h

theorem polynomialProfile_unit {m : ℕ} (hk : 2 ≤ k)
    (e : Fin k ≃ Option (Fin m)) : 1 ≤ polynomialProfile f e (fun _ => 1) :=
  one_le_onParties f e hk (PolynomialProduct.tensor_ne_zero _ (fun _ => by decide))

theorem polynomialProfile_upper {m : ℕ} (hk : 2 ≤ k)
    (e : Fin k ≃ Option (Fin m)) (n : ℕ) :
    polynomialProfile f e (fun _ => n) ≤
      ((1 + m * (n - 1) : ℕ) : ℝ) ^ (1 / meanExponent f) := by
  apply (onParties_le_rank f e hk _).trans
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    (by
      exact_mod_cast (show Tensor.rank (PolynomialProduct.tensor (fun _ : Fin m => n)) ≤
          1 + m * (n - 1) by
        simpa [PolynomialProduct.degree, Nat.add_comm] using
          PolynomialProduct.rank_tensor_le (fun _ : Fin m => n)))
    (one_div_nonneg.mpr (meanExponent_pos f hk).le)

theorem meanExponent_bound_inputs {m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    (e : Fin k ≃ Option (Fin m)) :
    meanExponent f ≤ ((m : ℝ) + 1) / (2 * m) := by
  have hp := meanExponent_pos f hk
  have h := Profile.exponent_le hm (polynomialProfile_nonnegative f e)
    (polynomialProfile_concavity f hk e) (polynomialProfile_tripling f hk e)
    (polynomialProfile_unit f hk e) (1 / meanExponent f) (by positivity)
    (fun n _ => polynomialProfile_upper f hk e n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h' := (le_div_iff₀ hp).mp h
  apply (le_div_iff₀ (mul_pos (by norm_num) hm0)).mpr
  have h'' := mul_le_mul_of_nonneg_right h' (show (0 : ℝ) ≤ m + 1 by positivity)
  have he : 2 * (m : ℝ) / (m + 1) * meanExponent f * (m + 1) =
      2 * m * meanExponent f := by
    field_simp [ne_of_gt (show (0 : ℝ) < m + 1 by positivity)]
  rw [he] at h''
  nlinarith

theorem meanExponent_le (hk : 2 ≤ k) :
    meanExponent f ≤ (k : ℝ) / (2 * (k - 1)) := by
  have hm : 1 ≤ k - 1 := by omega
  let e : Fin k ≃ Option (Fin (k - 1)) :=
    Fintype.equivOfCardEq (by simp; omega)
  have h := meanExponent_bound_inputs f hk hm e
  have he : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  simpa only [he, sub_add_cancel] using h

theorem Character.sum_pairExponent_le (hk : 2 ≤ k) :
    (∑ e, f.pairExponent e) ≤ (k : ℝ) ^ 2 / 4 := by
  have h := meanExponent_le f hk
  have hc : (0 : ℝ) < k.choose 2 := by exact_mod_cast Nat.choose_pos hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have hh : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
    linarith
  have hchoose : (k.choose 2 : ℝ) = (k : ℝ) * (k - 1) / 2 := Nat.cast_choose_two ℝ k
  rw [meanExponent] at h
  have hh := (div_le_iff₀ hc).mp h
  have he : (k : ℝ) / (2 * (k - 1)) * (k.choose 2 : ℝ) = (k : ℝ) ^ 2 / 4 := by
    rw [hchoose]
    field_simp [ne_of_gt hk1]
    ring
  exact hh.trans_eq he

end Lemmata.TensorRank.TensorSemiring

namespace Lemmata.TensorRank

theorem graphExponent_le_quarter_square (k : ℕ) (hk : 2 ≤ k) :
    graphExponent k ≤ (k : ℝ) ^ 2 / 4 := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have h : Tensor.asymptoticRank (completeGraph k 2) ≤ (2 : ℝ) ^ ((k : ℝ) ^ 2 / 4) := by
    apply (TensorSemiring.asymptoticRank_le_iff_characters hk _ _).mpr
    intro f
    rw [f.eval_completeGraph (by decide)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (f.sum_pairExponent_le hk)
  rw [asymptoticRank_completeGraph (by decide)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h

end Lemmata.TensorRank
