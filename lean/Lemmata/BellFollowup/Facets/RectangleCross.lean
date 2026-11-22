module

public import Lemmata.BellFollowup.Facets.Rectangle
public import Lemmata.BellFollowup.Facets.Transport

/-! # The original affine-equivalence statement at three parties and four settings -/

@[expose] public section
noncomputable section
open Set Lemmata.SymmetricBellCrossPolytope
namespace Lemmata.BellFollowup.Facets

/-- Rescale the two rectangle axes and take their half-sum and half-difference. -/
def toDiamond : (ℝ × ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.1/16 + z.2/24, z.1/16 - z.2/24]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

theorem toDiamond_injective : Function.Injective toDiamond := by
  intro x y h
  have e₀ := congrFun h 0
  have e₁ := congrFun h 1
  change x.1/16 + x.2/24 = y.1/16 + y.2/24 at e₀
  change x.1/16 - x.2/24 = y.1/16 - y.2/24 at e₁
  exact Prod.ext (by linarith) (by linarith)

theorem toDiamond_image : toDiamond '' chartPolytope = crossHull (Finset.univ : Finset (Fin 2)) := by
  let C : Set (ℝ × ℝ) := ({-8,8} : Set ℝ) ×ˢ ({-12,12} : Set ℝ)
  have rectangle : chartPolytope = convexHull ℝ C := by
    rw [chartPolytope_eq_rectangle]
    dsimp [C]
    rw [convexHull_prod, convexHull_pair, convexHull_pair,
      segment_eq_Icc (by norm_num : (-8 : ℝ) ≤ 8), segment_eq_Icc (by norm_num : (-12 : ℝ) ≤ 12)]
  have pp : toDiamond (8,12) = Pi.single 0 1 := by
    funext i; fin_cases i <;> norm_num [toDiamond,Pi.single_apply]
  have pn : toDiamond (8,-12) = Pi.single 1 1 := by
    funext i; fin_cases i <;> norm_num [toDiamond,Pi.single_apply]
  have nn : toDiamond (-8,-12) = -Pi.single 0 1 := by
    funext i; fin_cases i <;> norm_num [toDiamond,Pi.single_apply]
  have np : toDiamond (-8,12) = -Pi.single 1 1 := by
    funext i; fin_cases i <;> norm_num [toDiamond,Pi.single_apply]
  rw [rectangle,toDiamond.image_convexHull,crossHull]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩, rfl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨0,Finset.mem_univ _,Or.inr nn⟩
    · exact ⟨1,Finset.mem_univ _,Or.inr np⟩
    · exact ⟨1,Finset.mem_univ _,Or.inl pn⟩
    · exact ⟨0,Finset.mem_univ _,Or.inl pp⟩
  · rintro ⟨j,_,h | h⟩
    · fin_cases j
      · exact ⟨(8,12), by simp [C], pp.trans h.symm⟩
      · exact ⟨(8,-12), by simp [C], pn.trans h.symm⟩
    · fin_cases j
      · exact ⟨(-8,-12), by simp [C], nn.trans h.symm⟩
      · exact ⟨(-8,12), by simp [C], np.trans h.symm⟩

/-- Exactly the affirmative instance of the archive's claim at N=3,m=4
once the two explicit Reynolds-coordinate identities have been supplied. -/
theorem reynolds_cross_four (R : (ℝ × ℝ) →L[ℝ] V)
    (hchart : ∀ v : V, chart (Gamma 3 4 v) = chart v)
    (hrec : ∀ v : V, R (chart v) = Gamma 3 4 v) :
    ∃ f : V →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn f (Gamma 3 4 '' P) ∧ f '' (Gamma 3 4 '' P) = crossPolytope 2 := by
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let L := e.toLinearEquiv.toLinearMap.comp (toDiamond.comp (d0.prod d13).toLinearMap)
  refine ⟨L.toAffineMap, ?_, ?_⟩
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ h
    change e (toDiamond (chart (Gamma 3 4 x))) = e (toDiamond (chart (Gamma 3 4 y))) at h
    have eq := toDiamond_injective (e.injective h)
    rw [hchart x,hchart y] at eq
    exact (hrec x).symm.trans ((congrArg R eq).trans (hrec y))
  · change (fun v => e (toDiamond (chart v))) '' (Gamma 3 4 '' P) = e '' crossHull _
    rw [← toDiamond_image]
    ext z
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,by simpa only [hchart]⟩
    · rintro ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
      exact ⟨_,⟨x,hx,rfl⟩,by simp only [hchart]⟩

end Lemmata.BellFollowup.Facets
