module

public import Lemmata.RM59.Proof.CubicAction
public import Lemmata.RM59.Proof.CatalogTheory
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Lemmata.RM59.ColorRefinement

open scoped BigOperators

variable {n : ℕ}

def Invariant (P : CoordinateGroup n → Prop) (color : Point n → ℕ) : Prop :=
  ∀ g, P g → ∀ v, color (g v) = color v

theorem Invariant.mono {P Q : CoordinateGroup n → Prop} {color : Point n → ℕ}
    (h : Invariant P color) (hQP : ∀ g, Q g → P g) : Invariant Q color :=
  fun g hg v => h g (hQP g hg) v

def compressed {K : Type*} (key : Point n → K) (encode : K → ℕ) : Point n → ℕ :=
  fun v => encode (key v)

theorem compressed_invariant {K : Type*} (P : CoordinateGroup n → Prop)
    (key : Point n → K) (encode : K → ℕ)
    (hkey : ∀ g, P g → ∀ v, key (g v) = key v) :
    Invariant P (compressed key encode) := by
  intro g hg v
  unfold compressed
  rw [hkey g hg v]

theorem invariant_of_key_functionality {K : Type*} (P : CoordinateGroup n → Prop)
    (key : Point n → K) (color : Point n → ℕ)
    (hkey : ∀ g, P g → ∀ v, key (g v) = key v)
    (hfunction : ∀ v w, key v = key w → color v = color w) : Invariant P color := by
  intro g hg v
  exact hfunction (g v) v (hkey g hg v)

def graphKey (adj : Point n → Point n → Bool) (mark : Point n → ℕ) (v : Point n) : List ℕ :=
  [mark v, CatalogInvariant.degree adj v,
    CatalogInvariant.featureA adj v, CatalogInvariant.featureB adj v]

theorem graphKey_equiv (adj : Point n → Point n → Bool) (mark : Point n → ℕ)
    (g : CoordinateGroup n) (hadj : ∀ v w, adj (g v) (g w) = adj v w)
    (hmark : ∀ v, mark (g v) = mark v) (v : Point n) :
    graphKey adj mark (g v) = graphKey adj mark v := by
  have hd := CatalogInvariant.degree_equiv adj adj g.toEquiv hadj v
  have hA := CatalogInvariant.featureA_equiv adj adj g.toEquiv hadj v
  have hB := CatalogInvariant.featureB_equiv adj adj g.toEquiv hadj v
  change CatalogInvariant.degree adj v = CatalogInvariant.degree adj (g v) at hd
  change CatalogInvariant.featureA adj v = CatalogInvariant.featureA adj (g v) at hA
  change CatalogInvariant.featureB adj v = CatalogInvariant.featureB adj (g v) at hB
  unfold graphKey
  rw [hmark v, ← hd, ← hA, ← hB]

theorem graphColors_invariant (P : CoordinateGroup n → Prop)
    (adj : Point n → Point n → Bool) (mark : Point n → ℕ) (encode : List ℕ → ℕ)
    (hadj : ∀ g, P g → ∀ v w, adj (g v) (g w) = adj v w)
    (hmark : ∀ g, P g → ∀ v, mark (g v) = mark v) :
    Invariant P (compressed (graphKey adj mark) encode) := by
  apply compressed_invariant
  intro g hg v
  exact graphKey_equiv adj mark g (hadj g hg) (hmark g hg) v

def pairCode (a b : ℕ) : ℕ := min a b * 1024 + max a b

def additionProfile (color : Point n → ℕ) (v : Point n) : Multiset ℕ :=
  ∑ w, ({pairCode (color w) (color (w + v))} : Multiset ℕ)

def additionKey (color : Point n → ℕ) (v : Point n) : List ℕ :=
  color v :: (additionProfile color v).sort (· ≤ ·)

theorem additionProfile_equiv (color : Point n → ℕ) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v) (v : Point n) :
    additionProfile color (g v) = additionProfile color v := by
  symm
  unfold additionProfile
  apply Fintype.sum_equiv g.toEquiv _ _
  intro w
  change ({pairCode (color w) (color (w + v))} : Multiset ℕ) =
    {pairCode (color (g w)) (color (g w + g v))}
  rw [← g.map_add, hc w, hc (w + v)]

theorem additionKey_equiv (color : Point n → ℕ) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v) (v : Point n) :
    additionKey color (g v) = additionKey color v := by
  unfold additionKey
  rw [hc v, additionProfile_equiv color g hc v]

theorem additionColors_invariant (P : CoordinateGroup n → Prop) (color : Point n → ℕ)
    (encode : List ℕ → ℕ) (hc : Invariant P color) :
    Invariant P (compressed (additionKey color) encode) := by
  apply compressed_invariant
  intro g hg v
  exact additionKey_equiv color g (hc g hg) v

def neighborProfile (adj : Point n → Point n → Bool) (color : Point n → ℕ)
    (v : Point n) : Multiset ℕ :=
  ∑ w, if adj v w then ({color w} : Multiset ℕ) else 0

def ordinaryKey (adj : Point n → Point n → Bool) (anchors : List (Point n))
    (color : Point n → ℕ) (v : Point n) : List ℕ :=
  [color v] ++ anchors.map (fun a => color (v + a)) ++ (neighborProfile adj color v).sort (· ≤ ·)

theorem neighborProfile_equiv (adj : Point n → Point n → Bool) (color : Point n → ℕ)
    (g : CoordinateGroup n) (hc : ∀ v, color (g v) = color v)
    (hadj : ∀ v w, adj (g v) (g w) = adj v w) (v : Point n) :
    neighborProfile adj color (g v) = neighborProfile adj color v := by
  symm
  unfold neighborProfile
  apply Fintype.sum_equiv g.toEquiv _ _
  intro w
  change (if adj v w then ({color w} : Multiset ℕ) else 0) =
    (if adj (g v) (g w) then ({color (g w)} : Multiset ℕ) else 0)
  rw [hadj v w, hc w]

theorem ordinaryKey_equiv (adj : Point n → Point n → Bool) (anchors : List (Point n))
    (color : Point n → ℕ) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v)
    (hadj : ∀ v w, adj (g v) (g w) = adj v w)
    (ha : ∀ a ∈ anchors, g a = a) (v : Point n) :
    ordinaryKey adj anchors color (g v) = ordinaryKey adj anchors color v := by
  have hshift : anchors.map (fun a => color (g v + a)) =
      anchors.map (fun a => color (v + a)) := by
    apply List.map_congr_left
    intro a hamem
    simpa only [map_add, ha a hamem] using hc (v + a)
  unfold ordinaryKey
  rw [hc v, hshift, neighborProfile_equiv adj color g hc hadj v]

theorem ordinaryColors_invariant (P : CoordinateGroup n → Prop)
    (adj : Point n → Point n → Bool) (anchors : List (Point n)) (color : Point n → ℕ)
    (encode : List ℕ → ℕ) (hc : Invariant P color)
    (hadj : ∀ g, P g → ∀ v w, adj (g v) (g w) = adj v w)
    (ha : ∀ g, P g → ∀ a ∈ anchors, g a = a) :
    Invariant P (compressed (ordinaryKey adj anchors color) encode) := by
  apply compressed_invariant
  intro g hg v
  exact ordinaryKey_equiv adj anchors color g (hc g hg) (hadj g hg) (ha g hg) v

def shiftKey (anchors : List (Point n)) (color : Point n → ℕ) (v : Point n) : List ℕ :=
  color v :: anchors.map (fun a => color (v + a))

theorem shiftKey_equiv (anchors : List (Point n)) (color : Point n → ℕ)
    (g : CoordinateGroup n) (hc : ∀ v, color (g v) = color v)
    (ha : ∀ a ∈ anchors, g a = a) (v : Point n) :
    shiftKey anchors color (g v) = shiftKey anchors color v := by
  unfold shiftKey
  rw [hc v]
  congr 1
  apply List.map_congr_left
  intro a hamem
  simpa only [map_add, ha a hamem] using hc (v + a)

theorem shiftColors_invariant (P : CoordinateGroup n → Prop)
    (anchors : List (Point n)) (color : Point n → ℕ) (encode : List ℕ → ℕ)
    (hc : Invariant P color) (ha : ∀ g, P g → ∀ a ∈ anchors, g a = a) :
    Invariant P (compressed (shiftKey anchors color) encode) := by
  apply compressed_invariant
  intro g hg v
  exact shiftKey_equiv anchors color g (hc g hg) (ha g hg) v

def functionalHistogram (color : Point n → ℕ) (palette : List ℕ)
    (functional : Point n → Field) : List ℕ :=
  palette.map fun r => ∑ w, if color w = r ∧ functional w = 1 then 1 else 0

theorem functionalHistogram_equiv (color : Point n → ℕ) (palette : List ℕ)
    (functional functional' : Point n → Field) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v)
    (hf : ∀ w, functional' (g w) = functional w) :
    functionalHistogram color palette functional' = functionalHistogram color palette functional := by
  unfold functionalHistogram
  apply List.map_congr_left
  intro r _
  symm
  apply Fintype.sum_equiv g.toEquiv _ _
  intro w
  change (if color w = r ∧ functional w = 1 then 1 else 0) =
    (if color (g w) = r ∧ functional' (g w) = 1 then 1 else 0)
  rw [hc w, hf w]

def bilinearHistogram (t : Point n → Point n → Point n → Field) (color : Point n → ℕ)
    (palette : List ℕ) (a v : Point n) : List ℕ :=
  functionalHistogram color palette (fun w => t a v w)

theorem bilinearHistogram_equiv (t : Point n → Point n → Point n → Field)
    (color : Point n → ℕ) (palette : List ℕ) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v)
    (ht : ∀ u v w, t (g u) (g v) (g w) = t u v w)
    (a : Point n) (ha : g a = a) (v : Point n) :
    bilinearHistogram t color palette a (g v) = bilinearHistogram t color palette a v := by
  apply functionalHistogram_equiv color palette _ _ g hc
  intro w
  simpa only [ha] using ht a v w

def bilinearKey (t : Point n → Point n → Point n → Field) (anchors : List (Point n))
    (palette : List ℕ) (color : Point n → ℕ) (encodeHistogram : List ℕ → ℕ)
    (v : Point n) : List ℕ :=
  color v :: anchors.map (fun a => encodeHistogram (bilinearHistogram t color palette a v))

theorem bilinearKey_equiv (t : Point n → Point n → Point n → Field)
    (anchors : List (Point n)) (palette : List ℕ) (color : Point n → ℕ)
    (encodeHistogram : List ℕ → ℕ) (g : CoordinateGroup n)
    (hc : ∀ v, color (g v) = color v)
    (ht : ∀ u v w, t (g u) (g v) (g w) = t u v w)
    (ha : ∀ a ∈ anchors, g a = a) (v : Point n) :
    bilinearKey t anchors palette color encodeHistogram (g v) =
      bilinearKey t anchors palette color encodeHistogram v := by
  unfold bilinearKey
  rw [hc v]
  congr 1
  apply List.map_congr_left
  intro a hamem
  rw [bilinearHistogram_equiv t color palette g hc ht a (ha a hamem) v]

theorem bilinearColors_invariant (P : CoordinateGroup n → Prop)
    (t : Point n → Point n → Point n → Field) (anchors : List (Point n)) (palette : List ℕ)
    (color : Point n → ℕ) (encodeHistogram encodeKey : List ℕ → ℕ) (hc : Invariant P color)
    (ht : ∀ g, P g → ∀ u v w, t (g u) (g v) (g w) = t u v w)
    (ha : ∀ g, P g → ∀ a ∈ anchors, g a = a) :
    Invariant P (compressed (bilinearKey t anchors palette color encodeHistogram) encodeKey) := by
  apply compressed_invariant
  intro g hg v
  exact bilinearKey_equiv t anchors palette color encodeHistogram g (hc g hg) (ht g hg) (ha g hg) v

def individualizeKey (color : Point n → ℕ) (a v : Point n) : List ℕ :=
  [color v, if v = a then 1 else 0]

theorem individualizeColors_invariant (P : CoordinateGroup n → Prop) (color : Point n → ℕ)
    (a : Point n) (encode : List ℕ → ℕ) (hc : Invariant P color) :
    Invariant (fun g => P g ∧ g a = a) (compressed (individualizeKey color a) encode) := by
  apply compressed_invariant
  intro g hg v
  have heq : g v = a ↔ v = a := by
    constructor
    · intro h
      exact g.injective (h.trans hg.2.symm)
    · rintro rfl
      exact hg.2
  unfold individualizeKey
  rw [hc g hg.1 v]
  simp only [heq]

def colorClass (color : Point n → ℕ) (v : Point n) : Finset (Point n) :=
  Finset.univ.filter fun w => color w = color v

@[simp] theorem mem_colorClass (color : Point n → ℕ) (v w : Point n) :
    w ∈ colorClass color v ↔ color w = color v := by
  simp [colorClass]

theorem prefix_color_class_bound (H : Subgroup (CoordinateGroup n))
    (base : ℕ → Point n) (colors : ℕ → Point n → ℕ) (stages : ℕ)
    (hcolors : ∀ j, j < stages → Invariant
      (fun g : CoordinateGroup n => g ∈ H ∧ ∀ i, i < j → g (base i) = base i) (colors j))
    (hbase : ∀ g : H, (∀ j, j < stages → g • base j = base j) → g = 1) :
    Nat.card H ≤ ∏ j ∈ Finset.range stages, (colorClass (colors j) (base j)).card := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  apply prefix_stabilizer_chain_upper base (fun j => colorClass (colors j) (base j)) stages _ hbase
  intro j hj v hv
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hv
  apply (mem_colorClass _ _ _).mpr
  change colors j (((g : H) : CoordinateGroup n) (base j)) = colors j (base j)
  apply hcolors j hj ((g : H) : CoordinateGroup n) _ (base j)
  refine ⟨(g : H).property, ?_⟩
  intro i hi
  exact (mem_prefixStabilizer base j (g : H)).mp g.property i hi

theorem eq_one_of_injective_color (color : Point n → ℕ) (hinj : Function.Injective color)
    (g : CoordinateGroup n) (hc : ∀ v, color (g v) = color v) : g = 1 := by
  apply LinearEquiv.ext
  intro v
  change g v = v
  exact hinj (hc v)

theorem prefix_color_class_bound_of_terminal_injective (H : Subgroup (CoordinateGroup n))
    (base : ℕ → Point n) (colors : ℕ → Point n → ℕ) (stages : ℕ)
    (hcolors : ∀ j, j ≤ stages → Invariant
      (fun g : CoordinateGroup n => g ∈ H ∧ ∀ i, i < j → g (base i) = base i) (colors j))
    (hterminal : Function.Injective (colors stages)) :
    Nat.card H ≤ ∏ j ∈ Finset.range stages, (colorClass (colors j) (base j)).card := by
  apply prefix_color_class_bound H base colors stages
    (fun j hj => hcolors j (Nat.le_of_lt hj))
  intro g hfix
  apply Subtype.ext
  apply eq_one_of_injective_color (colors stages) hterminal
  apply hcolors stages le_rfl (g : CoordinateGroup n)
  exact ⟨g.property, hfix⟩

end Lemmata.RM59.ColorRefinement
