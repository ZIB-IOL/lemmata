module

public import Lemmata.SteinerSixSpectrum.Filling
public import Lemmata.SteinerSixSpectrum.Transversal

public section

namespace Lemmata.SteinerSixSpectrum

/-- On each master block take a copy of a six-column array. Its graphs cover
exactly the pairs over different points of that block. -/
private noncomputable def inflateBlock {X M A C : Type*}
    {row : A → C → M} (td : IsTransversal row)
    (B : Finset X) (size : B.card = 6) (col : B ≃ C) :
    PairDesign (Σ _ : X, M) (fun x y => x.1 ≠ y.1 ∧ x.1 ∈ B ∧ y.1 ∈ B) := by
  classical
  let graph (a : A) : B ↪ (Σ _ : X, M) :=
    ⟨fun i => ⟨i.val, row a (col i)⟩, fun _ _ h => Subtype.ext (congrArg Sigma.fst h)⟩
  let block (a : A) := Finset.univ.map (graph a)
  have mem (a : A) (x : Σ _ : X, M) :
      x ∈ block a ↔ ∃ h : x.1 ∈ B, row a (col ⟨x.1, h⟩) = x.2 := by
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨i.property, rfl⟩
    · rintro ⟨h, eq⟩
      exact Finset.mem_map.mpr ⟨⟨x.1,h⟩, Finset.mem_univ _, congrArg (Sigma.mk x.1) eq⟩
  refine ⟨Set.range block, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    simpa [block] using size
  · rintro _ ⟨a, rfl⟩ ⟨i,x⟩ hx ⟨j,y⟩ hy hne
    obtain ⟨hi, ex⟩ := (mem a _).mp hx
    obtain ⟨hj, ey⟩ := (mem a _).mp hy
    refine ⟨?_, hi, hj⟩
    intro eq
    change i = j at eq
    subst j
    exact hne (congrArg (Sigma.mk i) (ex.symm.trans ey))
  · rintro ⟨i,x⟩ ⟨j,y⟩ _ ⟨hne, hi, hj⟩
    have diff : col ⟨i,hi⟩ ≠ col ⟨j,hj⟩ := fun h => hne (congrArg Subtype.val (col.injective h))
    obtain ⟨a, ⟨hx, hy⟩, unique⟩ := td _ _ diff x y
    refine ⟨block a, ⟨⟨a, rfl⟩, (mem _ _).mpr ⟨hi, hx⟩, (mem _ _).mpr ⟨hj, hy⟩⟩, ?_⟩
    rintro _ ⟨⟨b, rfl⟩, bx, by'⟩
    exact congrArg block (unique b ⟨((mem _ _).mp bx).choose_spec, ((mem _ _).mp by').choose_spec⟩)

/-- A system on d points, a TD(6,m), and a filling of size m+e give an
S(2,6,d*m+e) for e = 0, 1, or 6. -/
theorem productStep {d m e : ℕ} {A C : Type*} [Fintype C] (six : Fintype.card C = 6)
    {row : A → C → Fin m} (td : IsTransversal row)
    (master : SteinerSystem (Fin d)) (shared : e = 0 ∨ e = 1 ∨ e = 6)
    (fill : Nonempty (SteinerSystem (Fin (m+e)))) :
    Nonempty (SteinerSystem (Fin (d*m+e))) := by
  classical
  let G (_ : Fin d) := Fin m
  let piece (B : ↥master.blocks) := inflateBlock td B.val (master.six B.val B.property)
    (Fintype.equivOfCardEq (by rw [Fintype.card_coe, master.six _ B.property, six]))
  have outer : PairDesign (Σ i, G i) (fun x y => x.1 ≠ y.1) := by
    apply PairDesign.assemble piece (fun _ _ _ h => h.1)
    intro x y _ h
    obtain ⟨B, ⟨hb, hx, hy⟩, unique⟩ := master.cover _ _ h trivial
    exact ⟨⟨B, hb⟩, ⟨h, hx, hy⟩, fun D hd => Subtype.ext (unique D.val ⟨D.property, hd.2⟩)⟩
  exact fillToOrder outer shared (fun _ => by simpa [G] using fill)
    (by simp [G, Fintype.card_sigma, Nat.add_comm])

end Lemmata.SteinerSixSpectrum
