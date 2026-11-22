module

public import Lemmata.SymmetricBellFacetLifting.Positive.Archive

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.SymmetricBellFacetLifting.Positive.Archive
open SymmetricBellCrossPolytope

def validRow {m : Nat} (a : Fin m → ℤ) : Prop := ∀ i, a i = 1 ∨ a i = -1

theorem valid_iff {m : Nat} (a : Fin m → ℤ) : List.ofFn a ∈ signRows m ↔ validRow a := by
  simp [mem_signRows, validRow]

theorem of_list {m : Nat} {l : List ℤ} (h : l ∈ signRows m) :
    ∃ a : Fin m → ℤ, List.ofFn a = l ∧ validRow a := by
  have hl := (mem_signRows.mp h).1
  subst m
  refine ⟨fun i => l[i.val], List.ofFn_getElem, (valid_iff _).mp ?_⟩
  simpa only [List.ofFn_getElem] using h

def triple {m : Nat} (a b c : Fin m → ℤ) : Tensor 3 m :=
  ivec fun x => a (x 0) * b (x 1) * c (x 2)

theorem triple_mem {m} {a b c : Fin m → ℤ}
    (ha : validRow a) (hb : validRow b) (hc : validRow c) : triple a b c ∈ strategySet 3 m := by
  refine ⟨![(fun i => (a i : ℝ)), (fun i => (b i : ℝ)), (fun i => (c i : ℝ))],?_,?_⟩
  · intro n i
    fin_cases n
    · change (a i : ℝ) = 1 ∨ (a i : ℝ) = -1
      rcases ha i with h|h <;> norm_num [h]
    · change (b i : ℝ) = 1 ∨ (b i : ℝ) = -1
      rcases hb i with h|h <;> norm_num [h]
    · change (c i : ℝ) = 1 ∨ (c i : ℝ) = -1
      rcases hc i with h|h <;> norm_num [h]
  · intro x
    simp [triple, ivec, Fin.prod_univ_three]

theorem exists_triple {m} {p : Tensor 3 m} (hp : p ∈ strategySet 3 m) :
    ∃ a b c : Fin m → ℤ, validRow a ∧ validRow b ∧ validRow c ∧ p = triple a b c := by
  obtain ⟨f,hf,he⟩ := hp
  let g (n : Fin 3) (i : Fin m) : ℤ := if f n i = 1 then 1 else -1
  have hg (n : Fin 3) : validRow (g n) := by intro i; dsimp [g]; split_ifs <;> simp
  have hc (n i) : (g n i : ℝ) = f n i := by rcases hf n i with h|h <;> norm_num [g,h]
  refine ⟨g 0,g 1,g 2,hg _,hg _,hg _,?_⟩
  apply PiLp.ext
  intro x
  rw [he]
  simp [Fin.prod_univ_three, triple, ivec, hc]

def score {m d} (A : Fin d → Index m → ℤ) (a b c : Fin m → ℤ) (i : Fin d) : ℤ :=
  ∑ x, A i x * (a (x 0) * b (x 1) * c (x 2))

theorem chart_triple {m d} (A : Fin d → Index m → ℤ) (D : Nat)
    (a b c : Fin m → ℤ) (i : Fin d) :
    linearChart A D (triple a b c) i = (score A a b c i : ℝ) / D := by
  rw [chartValue,PiLp.inner_apply]
  simp [ivec,triple,score,RCLike.inner_apply,mul_comm]

theorem chart_strategy {m d D} (A : Fin d → Index m → ℤ) (M : List (List ℤ))
    (compute : ∀ a b c : Fin m → ℤ, List.ofFn (score A a b c) =
      integerImage M (threeCoords m (List.ofFn a) (List.ofFn b) (List.ofFn c))) :
    linearChart A D '' strategySet 3 m = chartAtoms m d D M := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨a,b,c,ha,hb,hc,rfl⟩ := exists_triple hp
    exact ⟨_,(valid_iff a).mpr ha,_,(valid_iff b).mpr hb,_,(valid_iff c).mpr hc,
      _,(compute a b c).symm,chart_triple A D a b c⟩
  · rintro ⟨la,ha,lb,hb,lc,hc,z,hz,hx⟩
    obtain ⟨a,rfl,ha'⟩ := of_list ha
    obtain ⟨b,rfl,hb'⟩ := of_list hb
    obtain ⟨c,rfl,hc'⟩ := of_list hc
    have he : score A a b c = z := List.ofFn_injective ((compute a b c).trans hz)
    refine ⟨_,triple_mem ha' hb' hc',?_⟩
    ext i
    rw [chart_triple, he, ← hx i]

theorem archive_equivalence {m d D : Nat} (hD : 0 < D)
    (A : Fin d → Index m → ℤ) (M : List (List ℤ))
    (fixed : ∀ i, ivec (A i) ∈ symSub 3 m)
    (span : ∀ p ∈ symSub 3 m, p ∈ Submodule.span ℝ (range (fun i => ivec (A i))))
    (compute : ∀ a b c : Fin m → ℤ, List.ofFn (score A a b c) =
      integerImage M (threeCoords m (List.ofFn a) (List.ofFn b) (List.ofFn c)))
    (hull : convexHull ℝ (chartAtoms m d D M) = unitCross d) :
    ∃ f : Tensor 3 m →ᵃ[ℝ] EuclideanSpace ℝ (Fin d),
      InjOn f (Gamma 3 m '' localPolytope 3 m) ∧
      f '' (Gamma 3 m '' localPolytope 3 m) = crossPolytope d := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let L := linearChart A D
  refine ⟨e.toLinearMap.toAffineMap.comp L.toAffineMap,?_,?_⟩
  · intro x hx y hy he; exact chart_inj A D hD span hx hy (e.injective he)
  · change (fun p => e (L p)) '' _ = _
    rw [← Set.image_image, Set.image_image L (Gamma 3 m)]
    have heq : (fun p => L (Gamma 3 m p)) = L := funext (chart_project A D fixed)
    rw [heq]
    change e '' (linearChart A D '' convexHull ℝ (strategySet 3 m)) = _
    rw [LinearMap.image_convexHull, chart_strategy A M compute, hull]
    unfold crossPolytope crossHull unitCross
    congr 2
    ext z
    simp only [signedSet, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    suffices h : ∀ i : Fin d, axisVec i = Pi.single i (1:ℝ) by simp_rw [h]
    intro i
    ext j
    by_cases hij : i=j <;> simp [axisVec, hij, eq_comm]

/-- Expand a scalar sum over all setting triples in coordinate order. -/
theorem sum_indices {m} (f : Index m → ℤ) :
    ∑ x, f x = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, f ![i,j,k] := by
  let e : Index m ≃ (Fin m × Fin m × Fin m) := (tensorTowerTupleEquiv (Fin m) 2).symm
  have h : ∑ x, f x = ∑ t : Fin m × Fin m × Fin m, f ![t.1,t.2.1,t.2.2] := by
    apply Fintype.sum_equiv e
    intro x
    congr 1
    funext n
    fin_cases n <;> rfl
  rw [h,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]

end Lemmata.SymmetricBellFacetLifting.Positive.Archive
