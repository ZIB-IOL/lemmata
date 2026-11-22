module

public import Lemmata.ModifiedE8Bell.VectorValue
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

abbrev Correlation := Setting → Setting → ℝ
abbrev IntegerCorrelation := Setting → Setting → ℤ
abbrev Relabel := Array ℤ

/-- A deterministic bipartite correlation matrix. -/
def deterministic (a b : Signing) : Correlation := fun i j => (sign (a i) : ℝ) * (sign (b j) : ℝ)

/-- Membership in the full bipartite local correlation polytope. -/
def IsLocal (M : Correlation) : Prop :=
  M ∈ convexHull ℝ (Set.range fun ab : Signing × Signing => deterministic ab.1 ab.2)

lemma deterministic_local (a b : Signing) : IsLocal (deterministic a b) :=
  subset_convexHull ℝ _ ⟨(a,b),rfl⟩

lemma local_mix {A B : Correlation} (ha : IsLocal A) (hb : IsLocal B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1) : IsLocal (s • A + t • B) :=
  convex_convexHull ℝ _ ha hb hs ht hst

/-- A relabeling table uses signed one-based indices; the total definitions
also handle malformed indices. Locality does not require bijectivity. -/
def relIndex (r : Relabel) (i : Setting) : Setting :=
  ⟨((r[i.val]?.getD 1).natAbs - 1) % 120, Nat.mod_lt _ (by decide)⟩

def relFlip (r : Relabel) (i : Setting) : Bool := decide (r[i.val]?.getD 1 < 0)
def relSign (r : Relabel) (i : Setting) : ℤ := if relFlip r i then -1 else 1

def relSigning (r : Relabel) (a : Signing) (i : Setting) : Bool :=
  if relFlip r i then !(a (relIndex r i)) else a (relIndex r i)

lemma relSigning_sign (r : Relabel) (a : Signing) (i : Setting) :
    sign (relSigning r a i) = relSign r i * sign (a (relIndex r i)) := by
  unfold relSigning relSign
  cases h : relFlip r i <;> cases ha : a (relIndex r i) <;> simp [h,ha,sign]

/-- The linear action of a shared relabeling on correlations. -/
def relabelMap (r : Relabel) : Correlation →ₗ[ℝ] Correlation where
  toFun M i j := (relSign r i : ℝ) * (relSign r j : ℝ) * M (relIndex r i) (relIndex r j)
  map_add' A B := by ext i j; simp only [Pi.add_apply]; ring
  map_smul' c A := by ext i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma relabel_deterministic (r : Relabel) (a b : Signing) :
    relabelMap r (deterministic a b) = deterministic (relSigning r a) (relSigning r b) := by
  ext i j
  simp only [relabelMap, LinearMap.coe_mk, AddHom.coe_mk, deterministic, relSigning_sign, Int.cast_mul]
  ring

lemma relabel_local (r : Relabel) {M : Correlation} (hm : IsLocal M) : IsLocal (relabelMap r M) := by
  apply convexHull_min (t := (relabelMap r) ⁻¹' convexHull ℝ
      (Set.range fun ab : Signing × Signing => deterministic ab.1 ab.2)) ?_
      ((convex_convexHull ℝ _).linear_preimage (relabelMap r)) hm
  rintro _ ⟨⟨a,b⟩,rfl⟩
  change IsLocal (relabelMap r (deterministic a b))
  rw [relabel_deterministic]
  exact deterministic_local _ _

/-- Convert an integer numerator and positive integer denominator into correlations. -/
noncomputable def normalized (M : IntegerCorrelation) (d : ℕ) : Correlation :=
  fun i j => (M i j : ℝ) / (d : ℝ)

/-- A finite sum of relabelings, expressed as an integer correlation matrix. -/
def averageNumerator (rs : Array Relabel) (M : IntegerCorrelation) : IntegerCorrelation :=
  let A := Array.ofFn fun i : Setting => Array.ofFn fun j : Setting =>
    ∑ k : Fin rs.size, relSign rs[k] i * relSign rs[k] j * M (relIndex rs[k] i) (relIndex rs[k] j)
  fun i j => (A[i.val]?.getD #[])[j.val]?.getD 0

lemma averageNumerator_apply (rs : Array Relabel) (M : IntegerCorrelation) (i j : Setting) :
    averageNumerator rs M i j =
      ∑ k : Fin rs.size, relSign rs[k] i * relSign rs[k] j * M (relIndex rs[k] i) (relIndex rs[k] j) := by
  simp [averageNumerator]

lemma average_local (rs : Array Relabel) (hr : 0 < rs.size)
    (M : IntegerCorrelation) (d : ℕ) (hd : 0 < d) (hm : IsLocal (normalized M d)) :
    IsLocal (normalized (averageNumerator rs M) (rs.size*d)) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hr' : (rs.size : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have h := (convex_convexHull ℝ (Set.range fun ab : Signing × Signing => deterministic ab.1 ab.2)).sum_mem
    (t := (Finset.univ : Finset (Fin rs.size)))
    (w := fun _ => (rs.size : ℝ)⁻¹)
    (z := fun k => relabelMap rs[k] (normalized M d))
    (by intro k _; positivity)
    (by simp [hr'])
    (by intro k _; exact relabel_local _ hm)
  have he : normalized (averageNumerator rs M) (rs.size*d) =
      ∑ k : Fin rs.size, (rs.size : ℝ)⁻¹ • relabelMap rs[k] (normalized M d) := by
    ext i j
    simp only [normalized, averageNumerator_apply, Int.cast_sum, Int.cast_mul, Nat.cast_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, relabelMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  rw [he]
  exact h

end Lemmata.ModifiedE8Bell
