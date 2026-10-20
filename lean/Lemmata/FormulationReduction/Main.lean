module

public import Lemmata.FormulationReduction.Statement
public import Lemmata.NonnegativeRankReduction.Main
public import Lemmata.MatchingCostTransfer.Main
public import Lemmata.ObjectiveReversal.Main

@[expose] public section

namespace Lemmata.FormulationReduction

open scoped BigOperators
open Lemmata.SpanningTreeMinSplit
open Lemmata.NonnegativeRankReduction

variable {I J V : Type*} [AddCommGroup V] [Module ℝ V]
variable {value : I → J → ℝ} {bound : I → ℝ} {m : ℕ}

/-- Restrict objectives and realized solutions along independent maps without
changing the LP or its number of inequalities. For example, the solution map
can retain only perfect matchings among all feasible joins. -/
def CertifiedLP.pullback {I₀ J₀ : Type*}
    (C : CertifiedLP (V := V) value bound m) (f : I₀ → I) (g : J₀ → J) :
    CertifiedLP (V := V) (fun i j => value (f i) (g j)) (fun i => bound (f i)) m where
  constraintSlack := C.constraintSlack
  realization := fun j => C.realization (g j)
  feasible := fun l j => C.feasible l (g j)
  objective := fun i => C.objective (f i)
  realizes := fun i j => C.realizes (f i) (g j)
  multiplier := fun l i => C.multiplier l (f i)
  multiplier_nonneg := fun l i => C.multiplier_nonneg l (f i)
  offset := fun i => C.offset (f i)
  offset_nonneg := fun i => C.offset_nonneg (f i)
  certificate := fun i z => C.certificate (f i) z

/-- A certificate proves its objective lower bound throughout the feasible
region, rather than only at the realized solutions. -/
theorem certificate_sound (C : CertifiedLP (V := V) value bound m) (i : I) (z : V)
    (hz : ∀ l, 0 ≤ C.constraintSlack l z) :
    bound i ≤ C.objective i z := by
  have h : 0 ≤ C.objective i z - bound i := by
    rw [C.certificate]
    exact add_nonneg
      (Finset.sum_nonneg fun l _ => mul_nonneg (C.multiplier_nonneg l i) (hz l))
      (C.offset_nonneg i)
  exact sub_nonneg.mp h

/-- The factorization contributed by the inequalities, before adding the
nonnegative row offset. -/
def inequalityFactorization (C : CertifiedLP (V := V) value bound m) :
    NonnegativeFactorization
      (fun i j => ∑ l, C.multiplier l i * C.constraintSlack l (C.realization j)) m where
  left := C.multiplier
  right := fun l j => C.constraintSlack l (C.realization j)
  left_nonneg := C.multiplier_nonneg
  right_nonneg := C.feasible
  reconstruct := fun _ _ => rfl

/-- Evaluation of the affine certificates gives a factorization with at most
one more factor than the number of LP inequalities. -/
noncomputable def certifiedSlackFactorization (C : CertifiedLP (V := V) value bound m) :
    NonnegativeFactorization (fun i j => value i j - bound i) (m + 1) := by
  have h : (fun i j => value i j - bound i) =
      (fun i j =>
        (∑ l, C.multiplier l i * C.constraintSlack l (C.realization j)) + C.offset i) := by
    funext i j
    rw [← C.realizes i j, C.certificate]
  rw [h]
  exact factorRowOffset (inequalityFactorization C) C.offset C.offset_nonneg

/-- If every certificate has zero constant remainder, its slack factorization
uses precisely the `m` inequality factors, without an additional factor. -/
def certifiedSlackFactorizationZeroOffset (C : CertifiedLP (V := V) value bound m)
    (hzero : ∀ i, C.offset i = 0) :
    NonnegativeFactorization (fun i j => value i j - bound i) m := by
  have h : (fun i j => value i j - bound i) =
      (fun i j => ∑ l, C.multiplier l i * C.constraintSlack l (C.realization j)) := by
    funext i j
    rw [← C.realizes i j, C.certificate, hzero i, add_zero]
  rw [h]
  exact inequalityFactorization C

-- DOCS_BEGIN_MAIN
/-- The affine Farkas-certificate direction of formulation factorization.
Certificate existence is explicit in `CertifiedLP`. -/
theorem certified_slack_factorization : CertifiedSlackFactorization := by
  intro I J V _ _ value bound m C
  exact ⟨certifiedSlackFactorization C⟩

/-- A certified LP with `m` inequalities gives nonnegative rank at most `m+1`. -/
theorem certified_slack_rank_bound (C : CertifiedLP (V := V) value bound m) :
    nonnegativeRank (fun i j => value i j - bound i) ≤ ((m + 1 : ℕ) : ℕ∞) :=
  nonnegativeRank_le (certifiedSlackFactorization C)

/-- Zero constant remainders remove the extra factor. -/
theorem certified_slack_rank_bound_zero_offset
    (C : CertifiedLP (V := V) value bound m) (hzero : ∀ i, C.offset i = 0) :
    nonnegativeRank (fun i j => value i j - bound i) ≤ (m : ℕ∞) :=
  nonnegativeRank_le (certifiedSlackFactorizationZeroOffset C hzero)

/-- A source factorization lower bound transfers through a reduction with
nonnegative multiplier and remainder factorizations. The instance map `f`
and solution map `g` are independent; the matrices `A` and `B` can depend
on both indices. -/
theorem certified_reduction_lower_bound
    {I₀ J₀ : Type*} {S A B : I₀ → J₀ → ℝ} {a b L : ℕ}
    (C : CertifiedLP (V := V) value bound m)
    (FA : NonnegativeFactorization A a)
    (FB : NonnegativeFactorization B b)
    (f : I₀ → I) (g : J₀ → J)
    (h : ∀ i j, S i j = A i j * (value (f i) (g j) - bound (f i)) + B i j)
    (source_lower_bound : ∀ {k : ℕ}, NonnegativeFactorization S k → L ≤ k) :
    L ≤ a * (m + 1) + b := by
  exact source_lower_bound
    (factorReduction FA (certifiedSlackFactorization C) FB f g h)

/-- The same lower-bound transfer with the source hypothesis stated directly
as a bound on nonnegative rank. -/
theorem certified_reduction_rank_lower_bound
    {I₀ J₀ : Type*} {S A B : I₀ → J₀ → ℝ} {a b L : ℕ}
    (C : CertifiedLP (V := V) value bound m)
    (FA : NonnegativeFactorization A a)
    (FB : NonnegativeFactorization B b)
    (f : I₀ → I) (g : J₀ → J)
    (h : ∀ i j, S i j = A i j * (value (f i) (g j) - bound (f i)) + B i j)
    (source_lower_bound : (L : ℕ∞) ≤ nonnegativeRank S) :
    L ≤ a * (m + 1) + b := by
  exact ENat.natCast_le_natCast.mp
    (source_lower_bound.trans
      (nonnegativeRank_le (factorReduction FA (certifiedSlackFactorization C) FB f g h)))

/-- Zero constant remainders give the bound without the extra LP factor. -/
theorem certified_reduction_rank_lower_bound_zero_offset
    {I₀ J₀ : Type*} {S A B : I₀ → J₀ → ℝ} {a b L : ℕ}
    (C : CertifiedLP (V := V) value bound m)
    (hzero : ∀ i, C.offset i = 0)
    (FA : NonnegativeFactorization A a)
    (FB : NonnegativeFactorization B b)
    (f : I₀ → I) (g : J₀ → J)
    (h : ∀ i j, S i j = A i j * (value (f i) (g j) - bound (f i)) + B i j)
    (source_lower_bound : (L : ℕ∞) ≤ nonnegativeRank S) :
    L ≤ a * m + b := by
  exact ENat.natCast_le_natCast.mp
    (source_lower_bound.trans
      (nonnegativeRank_le
        (factorReduction FA (certifiedSlackFactorizationZeroOffset C hzero) FB f g h)))

/-- The positive-cost matching reduction, composed with the LP certificate
factorization. The lower bound for the shifted source is an explicit input. -/
theorem positive_cost_lp_lower_bound
    (q : I → J → ℝ) (α H : ℝ) {L : ℕ}
    (hα : 1 < α) (hH : 0 < H)
    (C : CertifiedLP (V := V)
      (fun i j => (2 * (α - 1) * H) * q i j + H)
      (fun _ => (2 * (α - 1) * H + H) / α) m)
    (source_lower_bound :
      (L : ℕ∞) ≤ nonnegativeRank (fun i j => q i j - 1 / (2 * α))) :
    L ≤ m + 1 :=
  Lemmata.MatchingCostTransfer.positive_cost_lower_bound q α H hα hH
    source_lower_bound (certifiedSlackFactorization C)

/-- If the positive-cost LP certificates have zero constant remainder,
the source lower bound applies directly to the number of inequalities. -/
theorem positive_cost_lp_lower_bound_zero_offset
    (q : I → J → ℝ) (α H : ℝ) {L : ℕ}
    (hα : 1 < α) (hH : 0 < H)
    (C : CertifiedLP (V := V)
      (fun i j => (2 * (α - 1) * H) * q i j + H)
      (fun _ => (2 * (α - 1) * H + H) / α) m)
    (hzero : ∀ i, C.offset i = 0)
    (source_lower_bound :
      (L : ℕ∞) ≤ nonnegativeRank (fun i j => q i j - 1 / (2 * α))) :
    L ≤ m :=
  Lemmata.MatchingCostTransfer.positive_cost_lower_bound q α H hα hH
    source_lower_bound (certifiedSlackFactorizationZeroOffset C hzero)

/-- A bounded baseline uses one factor for the LP's constant remainder and
one for the reduction's row correction. -/
theorem bounded_baseline_lp_lower_bound
    (q : I → J → ℝ) (a b : I → ℝ) (α B : ℝ) {L : ℕ}
    (hα : 1 < α) (ha : ∀ i, 0 < a i) (hbase : ∀ i, b i / a i ≤ B)
    (C : CertifiedLP (V := V) (fun i j => a i * q i j + b i)
      (fun i => (a i + b i) / α) m)
    (source_lower_bound : (L : ℕ∞) ≤ nonnegativeRank
      (fun i j => q i j - Lemmata.MatchingCostTransfer.retainedShift α B)) :
    L ≤ m + 2 := by
  exact Lemmata.MatchingCostTransfer.bounded_baseline_lower_bound q a b α B
    hα ha hbase source_lower_bound (certifiedSlackFactorization C)

/-- The near-exact objective-reversal transfer, composed with the LP certificate
factorization. Graph-specific maps and completion are explicit in `D`. -/
theorem near_exact_reversal_lp_lower_bound
    {S T : Type*} {sourceValue : I → S → ℝ} {cost : I → T → ℝ}
    {C opt : I → ℝ} {N : ℝ} {L : ℕ}
    (D : Lemmata.ObjectiveReversal.Reversal sourceValue cost (fun _ => N))
    (hN : 0 < N) (hopt : ∀ i, 0 ≤ opt i)
    (hmargin : ∀ i, 1 / 4 ≤ C i - opt i)
    (P : CertifiedLP (V := V) cost
      (fun i => (N - opt i) / (1 + 1 / (4 * N))) m)
    (source_lower_bound :
      (L : ℕ∞) ≤ nonnegativeRank (fun i s => C i - sourceValue i s)) :
    L ≤ m + 2 := by
  exact Lemmata.ObjectiveReversal.near_exact_rank_transfer D hN hopt hmargin
    source_lower_bound (certifiedSlackFactorization P)
-- DOCS_END_MAIN

end Lemmata.FormulationReduction
