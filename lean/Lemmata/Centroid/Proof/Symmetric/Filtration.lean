module

public import Lemmata.Centroid.Proof.Symmetric.Coordinates
public import Lemmata.Centroid.Proof.Linear.KernelJet

@[expose] public section

namespace Lemmata.Centroid.Symmetric

noncomputable section

variable {F I : Type*} [Field F] [Fintype I]

theorem contraction_comm (d : ℕ) (u v : I → F) (c : Coefficients F I (d + 2)) :
    contraction d u (contraction (d + 1) v c) =
      contraction d v (contraction (d + 1) u c) := by
  classical
  funext s
  simp only [contraction_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Sym.cons_swap]
  ring

theorem contraction_add_smul (d : ℕ) (u v : I → F) (t : F) :
    contraction d (u + t • v) = contraction d u + t • contraction d v := by
  classical
  ext c s
  simp [contraction_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem contraction_kernel_jet [Infinite F]
    (E : Submodule F (Coefficients F I 3)) (v u : I → F)
    (hmax : ∀ w : I → F,
      Module.finrank F (E.map (contraction 2 w)) ≤ Module.finrank F (E.map (contraction 2 v)))
    {c : Coefficients F I 3} (hc : c ∈ E) (hcv : contraction 2 v c = 0) :
    ∃ r : ℕ → Coefficients F I 3, (∀ n, r n ∈ E) ∧ r 0 = c ∧
      ∀ n, contraction 2 v (r (n + 1)) = -contraction 2 u (r n) := by
  let f := (contraction 2 v).domRestrict E
  let g := (contraction 2 u).domRestrict E
  have hmax' (t : F) : Module.finrank F (f + t • g).range ≤ Module.finrank F f.range := by
    have heq : f + t • g = (contraction 2 (v + t • u)).domRestrict E := by
      rw [contraction_add_smul]
      rfl
    rw [heq, LinearMap.range_domRestrict, LinearMap.range_domRestrict]
    exact hmax (v + t • u)
  obtain ⟨r, hr0, hr⟩ := Linear.maximal_rank_kernel_jet f g hmax' (x := ⟨c, hc⟩) hcv
  exact ⟨fun n => (r n).val, fun n => (r n).property, congrArg Subtype.val hr0, hr⟩

theorem contraction_jet_membership [Infinite F]
    (E : Submodule F (Coefficients F I 3)) (v u : I → F)
    (hmax : ∀ w : I → F,
      Module.finrank F (E.map (contraction 2 w)) ≤ Module.finrank F (E.map (contraction 2 v)))
    {c : Coefficients F I 3} (hc : c ∈ E) (hcv : contraction 2 v c = 0) :
    contraction 2 u c ∈ E.map (contraction 2 v) ∧
      contraction 1 u (contraction 2 u c) ∈
        (E.map (contraction 2 v)).map (contraction 1 v) ∧
      contraction 0 u (contraction 1 u (contraction 2 u c)) ∈
        ((E.map (contraction 2 v)).map (contraction 1 v)).map (contraction 0 v) := by
  obtain ⟨r, hrE, hr0, hr⟩ := contraction_kernel_jet E v u hmax hc hcv
  have h₁ : contraction 2 u c ∈ E.map (contraction 2 v) := by
    have hm : contraction 2 v (r 1) ∈ E.map (contraction 2 v) := ⟨r 1, hrE 1, rfl⟩
    have hn := (E.map (contraction 2 v)).neg_mem hm
    simpa only [hr 0, hr0, neg_neg] using hn
  have h₂ : contraction 1 v (contraction 2 v (r 2)) = contraction 1 u (contraction 2 u c) := by
    rw [hr 1, map_neg, contraction_comm 1 v u, hr 0, hr0, map_neg, neg_neg]
  have h₃ : contraction 0 v (contraction 1 v (contraction 2 v (r 3))) =
      -contraction 0 u (contraction 1 u (contraction 2 u c)) := by
    rw [hr 2, map_neg, map_neg, contraction_comm 1 v u, contraction_comm 0 v u, h₂]
  refine ⟨h₁, ⟨contraction 2 v (r 2), ⟨r 2, hrE 2, rfl⟩, h₂⟩, ?_⟩
  have hm : contraction 0 v (contraction 1 v (contraction 2 v (r 3))) ∈
      ((E.map (contraction 2 v)).map (contraction 1 v)).map (contraction 0 v) :=
    ⟨_, ⟨_, ⟨r 3, hrE 3, rfl⟩, rfl⟩, rfl⟩
  have hn := (((E.map (contraction 2 v)).map (contraction 1 v)).map (contraction 0 v)).neg_mem hm
  simpa only [h₃, neg_neg] using hn

theorem contraction_shadow_inclusions [Infinite F]
    (E S : Submodule F (Coefficients F I 3)) (v : I → F)
    (hSE : S ≤ E) (hSv : S ≤ (contraction 2 v).ker)
    (hmax : ∀ w : I → F,
      Module.finrank F (E.map (contraction 2 w)) ≤ Module.finrank F (E.map (contraction 2 v))) :
    quadraticShadow S ≤ E.map (contraction 2 v) ⊓ (contraction 1 v).ker ∧
      doubleShadow S ≤ (E.map (contraction 2 v)).map (contraction 1 v) ⊓ (contraction 0 v).ker ∧
      tripleShadow S ≤ ((E.map (contraction 2 v)).map (contraction 1 v)).map (contraction 0 v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · apply iSup_le
    intro i
    rintro q ⟨c, hc, rfl⟩
    let u : I → F := fun j => if j = i then 1 else 0
    have hjet := contraction_jet_membership E v u hmax (hSE hc) (hSv hc)
    refine ⟨?_, ?_⟩
    · change contractCoordinate i c ∈ E.map (contraction 2 v)
      simpa only [u, contraction_delta] using hjet.1
    · change contraction 1 v (contractCoordinate i c) = 0
      rw [← contraction_delta 2 i, contraction_comm 1 v u, hSv hc, map_zero]
  · apply Submodule.span_le.2
    rintro z ⟨u, c, hc, rfl⟩
    have hjet := contraction_jet_membership E v u hmax (hSE hc) (hSv hc)
    refine ⟨hjet.2.1, ?_⟩
    change contraction 0 v (contraction 1 u (contraction 2 u c)) = 0
    rw [contraction_comm 0 v u, contraction_comm 1 v u, hSv hc, map_zero, map_zero]
  · apply Submodule.span_le.2
    rintro z ⟨u, c, hc, rfl⟩
    exact (contraction_jet_membership E v u hmax (hSE hc) (hSv hc)).2.2

theorem finrank_inf_ker_add_map {U W : Type*}
    [AddCommGroup U] [Module F U] [Module.Finite F U]
    [AddCommGroup W] [Module F W]
    (P : Submodule F U) (f : U →ₗ[F] W) :
    Module.finrank F (P ⊓ f.ker : Submodule F U) + Module.finrank F (P.map f) =
      Module.finrank F P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have hker := Submodule.finrank_map_subtype_eq P (f.ker.comap P.subtype)
  rw [Submodule.map_comap_subtype] at hker
  omega

theorem contraction_filtration_bound [Infinite F]
    (E S : Submodule F (Coefficients F I 3)) (v : I → F)
    (hSE : S ≤ E) (hSv : S ≤ (contraction 2 v).ker)
    (hmax : ∀ w : I → F,
      Module.finrank F (E.map (contraction 2 w)) ≤ Module.finrank F (E.map (contraction 2 v))) :
    Module.finrank F (quadraticShadow S) + Module.finrank F (doubleShadow S) +
      Module.finrank F (tripleShadow S) ≤ Module.finrank F (E.map (contraction 2 v)) := by
  obtain ⟨hq, hd, ht⟩ := contraction_shadow_inclusions E S v hSE hSv hmax
  have hq' := Submodule.finrank_mono hq
  have hd' := Submodule.finrank_mono hd
  have ht' := Submodule.finrank_mono ht
  have h₁ := finrank_inf_ker_add_map (E.map (contraction 2 v)) (contraction 1 v)
  have h₂ := finrank_inf_ker_add_map ((E.map (contraction 2 v)).map (contraction 1 v)) (contraction 0 v)
  omega

end

end Lemmata.Centroid.Symmetric
