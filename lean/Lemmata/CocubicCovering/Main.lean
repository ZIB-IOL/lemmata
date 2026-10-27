module

public import Lemmata.CocubicCovering.Proof.MinRank
public meta import Lemmata.CocubicCovering.Proof.MinRank
public import Lemmata.CocubicCovering.Proof.StrongerResults
public meta import Lemmata.CocubicCovering.Proof.StrongerResults
public import Lemmata.CocubicCovering.Proof.ResultsMain
public meta import Lemmata.CocubicCovering.Proof.ResultsMain

@[expose] public section

set_option Elab.async false

namespace Lemmata.CocubicCovering

open Covering

-- DOCS_BEGIN_MAIN
theorem support_weight_bound {m : ℕ} (hm : 4 ≤ m) (f h : BooleanFunction m)
    (hf : f ∈ reedMuller m (m - 3)) (hh : h ∈ reedMuller m (m - 4)) :
    2 * Module.finrank Field (affineOnSupport (f + h)) + rank (pairing f h) ≤
      weight (f + h) :=
  weight_bound_of_pairing hm f h hf hh

-- Each triple indexes a cubic monomial; coordinates are numbered from zero.
theorem form9_bounds (h : BooleanFunction 9) (hh : h ∈ reedMuller 9 5) :
    (let F : CubicCoefficients 9 := fun s =>
       if s.val.image Fin.val ∈
          [{0, 3, 6}, {0, 4, 7}, {0, 5, 8}, {1, 3, 7}, {1, 4, 6}, {1, 4, 8},
           {1, 5, 6}, {2, 3, 8}, {2, 4, 6}, {2, 5, 7}, {2, 5, 8}, {6, 7, 8}]
       then 1 else 0
     let f := eval (cubicComplement F)
     12 ≤ rank (pairing f h) ∧ 32 ≤ weight (f + h)) :=
  ⟨form9_pairing_rank_ge_twelve h hh, form9_weight_ge_thirty_two h hh⟩

theorem form10_bounds (h : BooleanFunction 10) (hh : h ∈ reedMuller 10 6) :
    (let F : CubicCoefficients 10 := fun s =>
       if s.val.image Fin.val ∈
          [{0, 3, 6}, {0, 4, 7}, {0, 5, 8}, {1, 3, 7}, {1, 4, 6}, {1, 4, 8},
           {1, 5, 6}, {2, 3, 8}, {2, 4, 6}, {2, 5, 7}, {2, 5, 8}, {7, 8, 9}]
       then 1 else 0
     let f := eval (cubicComplement F)
     10 ≤ rank (pairing f h) ∧ 32 ≤ weight (f + h)) :=
  ⟨form10_pairing_rank_ge_ten h hh, form10_weight_ge_thirty_two h hh⟩

theorem form11_bounds (h : BooleanFunction 11) (hh : h ∈ reedMuller 11 7) :
    (let F : CubicCoefficients 11 := fun s =>
       if s.val.image Fin.val ∈
          [{0, 3, 6}, {0, 4, 7}, {0, 5, 8}, {1, 3, 7}, {1, 4, 6}, {1, 4, 8},
           {1, 5, 6}, {2, 3, 8}, {2, 4, 6}, {2, 5, 7}, {2, 5, 8}, {8, 9, 10}]
       then 1 else 0
     let f := eval (cubicComplement F)
     10 ≤ rank (pairing f h) ∧ 34 ≤ weight (f + h)) :=
  ⟨form11_pairing_rank_ge_ten h hh, form11_weight_ge_thirty_four h hh⟩
-- DOCS_END_MAIN

theorem cocubic_covering_lower_bound (m : ℕ) (hm : 9 ≤ m) :
    2 * m + 12 ≤ coveringRadius m (m - 4) (m - 3) :=
  CoveringGeneral.coveringRadius_ge_two_mul_add_twelve m hm

theorem nine_variable_covering_lower_bound : 32 ≤ coveringRadius 9 5 6 :=
  coveringRadius9_ge_thirty_two

end Lemmata.CocubicCovering
