module

public import Lemmata.SymmetricBellCrossPolytope.Main

@[expose] public section

open Set
open scoped Pointwise BigOperators

namespace Lemmata.SymmetricBellFacetLifting

open SymmetricBellCrossPolytope

/-- Flipping one party preserves locality and reverses every full correlator. -/
theorem neg_mem_local {N m : ℕ} {p : Tensor (N+1) m}
    (hp : p ∈ localPolytope (N+1) m) : -p ∈ localPolytope (N+1) m := by
  let S := strategySet (N+1) m
  have hS : ∀ u ∈ S, -u ∈ S := by
    intro u hu
    obtain ⟨a, ha, h⟩ := hu
    refine ⟨(fun i x => if i = 0 then -a i x else a i x), ?_, ?_⟩
    · intro i x
      by_cases h0 : i = 0
      · subst i
        rcases ha 0 x with ht | ht <;> simp [ht]
      · simpa [h0] using ha i x
    · intro x
      simp [PiLp.neg_apply, h x, Fin.prod_univ_succ]
  have hs : -S = S := by
    ext u
    change -u ∈ S ↔ u ∈ S
    exact ⟨fun hu => by simpa using hS _ hu, hS u⟩
  have hHull : -(convexHull ℝ S) = convexHull ℝ S := by
    rw [← convexHull_neg, hs]
  change -p ∈ convexHull ℝ S
  rw [← hHull]
  change - -p ∈ convexHull ℝ S
  rw [neg_neg]
  exact hp

/-- Every Reynolds-projected full-correlation local polytope is centrally symmetric. -/
theorem neg_mem_projected {N m : ℕ} {p : Tensor (N+1) m}
    (hp : p ∈ Gamma (N+1) m '' localPolytope (N+1) m) :
    -p ∈ Gamma (N+1) m '' localPolytope (N+1) m := by
  obtain ⟨u, hu, rfl⟩ := hp
  exact ⟨-u, neg_mem_local hu, map_neg _ _⟩

private theorem more_than_odd_family {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hneg : ∀ x ∈ S, -x ∈ S)
    (g : Fin 19 → E) (hg : Function.Injective g)
    (he : ∀ i, g i ∈ S.extremePoints ℝ) :
    ∃ f : Fin 20 → E, Function.Injective f ∧ ∀ i, f i ∈ S.extremePoints ℝ := by
  classical
  have hne : g 0 ≠ g 1 := fun h => (by decide : (0 : Fin 19) ≠ 1) (hg h)
  have hex : ∃ v ∈ S, v ≠ 0 := by
    by_cases h : g 0 = 0
    · exact ⟨g 1, (he 1).1, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨g 0, (he 0).1, h⟩
  have h0 : 0 ∉ S.extremePoints ℝ := by
    obtain ⟨v,hv,hv0⟩ := hex
    intro h
    have hs : (0:E) ∈ openSegment ℝ v (-v) := by
      simpa only [midpoint_self_neg] using midpoint_mem_openSegment (𝕜 := ℝ) v (-v)
    exact hv0 (h.2 hv (hneg v hv) hs)
  have closure : (LinearEquiv.neg ℝ : E ≃ₗ[ℝ] E) '' S = S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hneg x hx
    · intro hy
      exact ⟨-y,hneg y hy,neg_neg y⟩
  have extreme_neg (x : E) (hx : x ∈ S.extremePoints ℝ) : -x ∈ S.extremePoints ℝ := by
    have e := image_extremePoints (𝕜 := ℝ) (LinearEquiv.neg ℝ : E ≃ₗ[ℝ] E) S
    rw [closure] at e
    rw [← e]
    exact ⟨x,hx,rfl⟩
  have extra : ∃ i, -g i ∉ Set.range g := by
    by_contra! hall
    choose k hk using hall
    have hkk (i) : k (k i) = i := hg (by rw [hk, hk, neg_neg])
    have hki (i) : k i ≠ i := by
      intro hi
      have eqn := hk i
      rw [hi] at eqn
      have two : (2:ℝ) • g i = 0 := by
        calc
          _ = g i + g i := two_smul ℝ _
          _ = -g i + g i := congrArg (· + g i) eqn
          _ = 0 := neg_add_cancel _
      have zero : g i = 0 := (smul_eq_zero.mp two).resolve_left (by norm_num)
      exact h0 (zero ▸ he i)
    have p : (∏ _i : Fin 19, (-1:ℤ)) = 1 :=
      Finset.prod_ninvolution k (fun _ => by norm_num) (fun i _ => hki i)
        (fun _ => Finset.mem_univ _) hkk
    norm_num at p
  obtain ⟨i,hi⟩ := extra
  refine ⟨Fin.cons (-g i) g, Fin.cons_injective_of_injective hi hg, ?_⟩
  exact Fin.cases (extreme_neg _ (he i)) he

/-- Twenty distinct extreme points in the archive's three-party, 17-setting polytope. -/
theorem twenty_extreme : ∃ f : Fin 20 → Tensor 3 17, Function.Injective f ∧
    ∀ i, f i ∈ (Gamma 3 17 '' localPolytope 3 17).extremePoints ℝ := by
  obtain ⟨g,hg,he⟩ := nineteen_extreme
  exact more_than_odd_family (fun _ h => neg_mem_projected h) g hg he

end Lemmata.SymmetricBellFacetLifting
