module

public import Lemmata.SymmetricBellFacetLifting.Positive.Strategy
public import Lemmata.SymmetricBellFacetLifting.Positive.Main

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.SymmetricBellFacetLifting.Positive.Archive.M5
open SymmetricBellCrossPolytope
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def B (i : Fin 3) (x : Index 5) : ℤ :=
  let n := (x 0).val + (x 1).val + (x 2).val
  (-1) ^ (n / 5) * (if n % 5 = i.val then 1 else if i.val > 0 ∧ 5 - n % 5 = i.val then -1 else 0)

private def A (i : Fin 3) (x : Index 5) : ℤ :=
  ∑ r : Fin 3, (![![(100),(75),(25)],![(100),(-25),(-75)],![(24),(-26),(26)]] : Fin 3 → Fin 3 → ℤ) i r * B r x

private def C : Fin 3 → Fin 3 → ℤ := ![![(13),(13),(25)],![(22),(-10),(-50)],![(10),(-22),(50)]]
private def R (r : Fin 3) : Index 5 := ![0,0,Fin.ofNat 5 r.val]
private def W (x : Index 5) : List (Fin 4) :=
  ([
    [],[],[],[3],[3],[1],[0,1,2,0,1],[1,1,3,2,1],[1,1,3,2,1],[0,1,2],
    [1],[3,2,1,2],[0,1,3,2,2,1],[0,1,2,2],[2,1,2],[1,3],[3,2,1,2],[1,1,2,2],[0,1,2,2,1],[2,1,2],
    [1,3],[1,1,2],[1,1,2,1],[1,1,2,1],[2,1,2,3],[0,1],[1,2,0,1],[1,0,3,2,1],[1,0,3,2,1],[1,2],
    [2,0,1],[2,1,3,2,1],[1,2,1,3,2,1],[2,1,2,2],[1,2],[3,2,1],[3,2,2,1,2],[0,2,1,0,2,2],[0,1,2,2],[1,2],
    [3,2,1],[0,2,1,0,2],[1,1,2,2],[2,1,2,2],[1,2,3],[0,2],[0,2],[0,2],[3,2],[3,2],
    [0,1],[1,3,2,1],[1,3,2,2,1],[1,2,2],[1,2,1],[0,3,2,1],[2,1,3,2,1],[2,1,0,2,2],[1,2,2],[0,1,2],
    [3,2,2,1],[2,2,1,0,2],[2,1,0,2,2],[1,2,2],[2,0,1,2,3],[0,2,2],[0,2,2],[0,2,2],[3,2,2],[3,2,2],
    [0,2,1],[1,1,2],[2,1,3,2,2],[1,2,2,3],[0,2,0,1,2],[0,1,3],[1,3,2,1],[1,0,2,2],[1,2,2,1],[1,2,1],
    [0,3,2,1],[2,1,0,2],[1,0,2,2],[0,2,1,2,2],[0,1,2,3],[2,2],[2,2],[2,2],[2,2,3],[2,2,3],
    [2,2,1],[2,1,0,2],[1,3,2,2],[2,0,1,2,2,3],[2,2,0,1,2],[0,2,1],[0,1,3,2],[1,3,2,2],[0,2,0,1,2,2],[0,2,2,1,2],
    [0,1,3],[1,0,2],[1,0,2,1],[1,0,2,1],[1,2,1,3],[2],[2],[2],[2,3],[2,3],
    [2,1],[1,0,2],[3,2,1,2,2],[0,1,2,2,3],[2,0,1,2],[2,1],[1,3,2],[0,1,3,2,2],[2,0,1,2,2],[2,2,1,2],
    [2,1,3],[1,3,2],[2,1,1,2,2],[1,0,2,2,1,2],[2,2,1,2]] : List (List (Fin 4)))[(x 0).val*25+(x 1).val*5+(x 2).val]!

private theorem ok : generatorOK 5 := by
  have h : ∀ i : Fin 4, ∀ x : Index 5,
      ending ((![ [0],[1,1],List.replicate 4 2,[3]] : Fin 4 → List (Fin 4)) i) (idx i x) = x := by decide +kernel
  exact ⟨fun i => (show Function.LeftInverse _ _ from h i).injective, by decide +kernel⟩

private theorem basis_fixed (i : Fin 3) : ivec (A i) ∈ symSub 3 5 :=
  fixed_of_equivariance ok _ ((show ∀ (i : Fin 3) j x, weight j x * A i x = A i (idx j x) by decide +kernel) i)

private theorem basis_span : ∀ p ∈ symSub 3 5,
    p ∈ Submodule.span ℝ (range (fun j => ivec (A j))) := by
  apply span_of_reconstruction A B R C 3200 (by decide) (by decide +kernel)
  apply expand_fixed ok R B W
  decide +kernel

private theorem compute (a b c : Fin 5 → ℤ) :
    List.ofFn (score A a b c) = integerImage inv5 (threeCoords 5 (List.ofFn a) (List.ofFn b) (List.ofFn c)) := by
  change [score A a b c 0, score A a b c 1, score A a b c 2] = _
  simp only [score, sum_indices]
  have hr : List.range 5 = [0,1,2,3,4] := by decide
  have hd : List.range 3 = [0,1,2] := by decide
  norm_num [hr, hd, Fin.sum_univ_succ, List.ofFn_succ, A, B, integerImage, inv5,
    threeCoords, ncMul, evenCoords, List.zipWith, List.getElem!_cons_zero, List.getElem!_cons_succ] <;> (repeat' constructor) <;> ring

/-- The full archive affine-equivalence statement at three parties and 5 settings. -/
theorem positive : ∃ f : Tensor 3 5 →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
    InjOn f (Gamma 3 5 '' localPolytope 3 5) ∧
    f '' (Gamma 3 5 '' localPolytope 3 5) = crossPolytope 3 :=
  archive_equivalence (D := 3200) (by decide) _ _ basis_fixed basis_span compute positive_5

end Lemmata.SymmetricBellFacetLifting.Positive.Archive.M5
