module

public import Lemmata.TensorRank.Proof.SpectrumRank
public import Mathlib.Order.Zorn

@[expose] public section

set_option autoImplicit false

namespace Lemmata.TensorRank.Spectrum

variable {S : Type*} [CommSemiring S]

instance : Preorder (StrassenPreorder S) where
  le p q := ∀ a b, p.Rel a b → q.Rel a b
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hpq hqr := fun a b h => hqr a b (hpq a b h)

namespace StrassenPreorder

variable (p : StrassenPreorder S)

def AddCancellative : Prop := ∀ a b c, p.Rel (a + c) (b + c) → p.Rel a b

def MulCancellative : Prop := ∀ a b c, c ≠ 0 → p.Rel (a * c) (b * c) → p.Rel a b

private theorem not_add_one_self (a : S) : ¬ p.Rel (a + 1) a := by
  intro h
  have hi (n : ℕ) : p.Rel (a + (n : S)) a := by
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using p.refl a
    | succ n ih =>
      simpa only [Nat.cast_succ, add_assoc] using p.trans (p.add ih (p.refl 1)) h
  obtain ⟨n, hn⟩ := p.bounded a
  have hsmall : p.Rel ((n + 1 : ℕ) : S) (a + ((n + 1 : ℕ) : S)) := by
    simpa only [zero_add] using p.add (p.zero_le a) (p.refl ((n + 1 : ℕ) : S))
  have hnat := (p.nat_iff (n + 1) n).mp (p.trans (p.trans hsmall (hi (n + 1))) hn)
  omega

theorem nat_add_cancel {m n : ℕ} (c : S)
    (h : p.Rel ((m : S) + c) ((n : S) + c)) : m ≤ n := by
  by_contra hmn
  have hstep := p.trans (p.add ((p.nat_iff (n + 1) m).mpr (by omega)) (p.refl c)) h
  apply p.not_add_one_self ((n : S) + c)
  convert hstep using 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

def addClosure : StrassenPreorder S where
  Rel a b := ∃ c, p.Rel (a + c) (b + c)
  refl a := ⟨0, p.refl _⟩
  trans := by
    rintro a b d ⟨c, h⟩ ⟨e, g⟩
    exact ⟨c + b + e, by convert p.add h g using 1 <;> ring⟩
  zero_le a := ⟨0, by simpa only [add_zero] using p.zero_le a⟩
  nat_iff m n := ⟨fun ⟨c, h⟩ => p.nat_add_cancel c h,
    fun h => ⟨0, by simpa only [add_zero] using (p.nat_iff m n).mpr h⟩⟩
  add := by
    rintro a b c d ⟨u, h⟩ ⟨v, g⟩
    exact ⟨u + v, by convert p.add h g using 1 <;> ring⟩
  mul := by
    rintro a b c d ⟨u, h⟩ ⟨v, g⟩
    refine ⟨u * c + b * c + b * v, ?_⟩
    convert p.add (p.mul h (p.refl c)) (p.mul g (p.refl b)) using 1 <;> ring
  cofinal a b hb := by
    obtain ⟨n, hn⟩ := p.cofinal a b hb
    exact ⟨n, 0, by simpa only [add_zero] using hn⟩

theorem maximal_addCancellative (hm : IsMax p) : p.AddCancellative := by
  have he : p ≤ p.addClosure := fun _ _ h => ⟨0, by simpa only [add_zero] using h⟩
  exact fun a b c h => (hm he) a b ⟨c, h⟩

include p in
theorem mul_ne_zero {a b : S} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  obtain ⟨m, hm⟩ := p.cofinal 1 a ha
  obtain ⟨n, hn⟩ := p.cofinal 1 b hb
  have he : ((m : S) * a) * ((n : S) * b) = 0 := by
    calc
      _ = ((m : S) * n) * (a * b) := by ring
      _ = 0 := by rw [hab, mul_zero]
  have h : p.Rel (1 : S) 0 := by simpa only [one_mul, he] using p.mul hm hn
  have := (p.nat_iff 1 0).mp (by simpa only [Nat.cast_one, Nat.cast_zero] using h)
  omega

theorem nat_mul_cancel (hc : p.AddCancellative) {m n : ℕ} {c : S} (hcz : c ≠ 0)
    (h : p.Rel ((m : S) * c) ((n : S) * c)) : m ≤ n := by
  by_contra hmn
  have hs := p.trans (p.mul ((p.nat_iff (n + 1) m).mpr (by omega)) (p.refl c)) h
  have hz : p.Rel c 0 := hc c 0 ((n : S) * c) (by
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, zero_add, add_zero, add_comm] using hs)
  obtain ⟨r, hr⟩ := p.cofinal 1 c hcz
  have hzero : p.Rel (1 : S) 0 := p.trans hr (by
    simpa only [mul_zero] using p.mul (p.refl (r : S)) hz)
  have := (p.nat_iff 1 0).mp (by simpa only [Nat.cast_one, Nat.cast_zero] using hzero)
  omega

def mulClosure (hc : p.AddCancellative) : StrassenPreorder S where
  Rel a b := ∃ c, c ≠ 0 ∧ p.Rel (a * c) (b * c)
  refl a := ⟨1, p.one_ne_zero, p.refl _⟩
  trans := by
    rintro a b d ⟨c, hc, h⟩ ⟨e, he, g⟩
    refine ⟨c * e, p.mul_ne_zero hc he, ?_⟩
    have hg : p.Rel ((b * c) * e) ((d * c) * e) := by
      convert p.mul g (p.refl c) using 1 <;> ring
    simpa only [mul_assoc] using p.trans (p.mul h (p.refl e)) hg
  zero_le a := ⟨1, p.one_ne_zero, by simpa only [mul_one] using p.zero_le a⟩
  nat_iff m n := ⟨fun ⟨c, hcz, h⟩ => p.nat_mul_cancel hc hcz h,
    fun h => ⟨1, p.one_ne_zero, by simpa only [mul_one] using (p.nat_iff m n).mpr h⟩⟩
  add := by
    rintro a b c d ⟨u, hu, h⟩ ⟨v, hv, g⟩
    refine ⟨u * v, p.mul_ne_zero hu hv, ?_⟩
    convert p.add (p.mul h (p.refl v)) (p.mul g (p.refl u)) using 1 <;> ring
  mul := by
    rintro a b c d ⟨u, hu, h⟩ ⟨v, hv, g⟩
    exact ⟨u * v, p.mul_ne_zero hu hv, by convert p.mul h g using 1 <;> ring⟩
  cofinal a b hb := by
    obtain ⟨n, hn⟩ := p.cofinal a b hb
    exact ⟨n, 1, p.one_ne_zero, by simpa only [mul_one] using hn⟩

theorem maximal_mulCancellative (hm : IsMax p) : p.MulCancellative := by
  have he : p ≤ p.mulClosure (p.maximal_addCancellative hm) :=
    fun _ _ h => ⟨1, p.one_ne_zero, by simpa only [mul_one] using h⟩
  exact fun a b c hc h => (hm he) a b ⟨c, hc, h⟩

def comparisonExtension (hc : p.AddCancellative) (hm : p.MulCancellative)
    (a b : S) (hab : ¬ p.Rel a b) : StrassenPreorder S where
  Rel x y := ∃ s, p.Rel (x + s * a) (y + s * b)
  refl x := ⟨0, by simpa only [zero_mul, add_zero] using p.refl x⟩
  trans := by
    rintro x y z ⟨s, h⟩ ⟨t, g⟩
    refine ⟨s + t, hc _ _ y ?_⟩
    convert p.add h g using 1 <;> ring
  zero_le x := ⟨0, by simpa only [zero_mul, add_zero] using p.zero_le x⟩
  nat_iff m n := by
    constructor
    · rintro ⟨s, h⟩
      by_contra hmn
      by_cases hs : s = 0
      · subst s
        have h' : m ≤ n := (p.nat_iff m n).mp (by simpa only [zero_mul, add_zero] using h)
        omega
      · have h' := p.trans (p.add ((p.nat_iff n m).mpr (by omega)) (p.refl (s * a))) h
        have h'' : p.Rel (s * a) (s * b) := hc _ _ (n : S) (by convert h' using 1 <;> ring)
        exact hab (hm a b s hs (by simpa only [mul_comm] using h''))
    · intro h
      exact ⟨0, by simpa only [zero_mul, add_zero] using (p.nat_iff m n).mpr h⟩
  add := by
    rintro x y u v ⟨s, h⟩ ⟨t, g⟩
    exact ⟨s + t, by convert p.add h g using 1 <;> ring⟩
  mul := by
    rintro x y u v ⟨s, h⟩ ⟨t, g⟩
    refine ⟨s * u + t * y, hc _ _ (y * u) ?_⟩
    convert p.add (p.mul h (p.refl u)) (p.mul g (p.refl y)) using 1 <;> ring
  cofinal x y hy := by
    obtain ⟨n, hn⟩ := p.cofinal x y hy
    exact ⟨n, 0, by simpa only [zero_mul, add_zero] using hn⟩

theorem maximal_total (hm : IsMax p) (a b : S) : p.Rel a b ∨ p.Rel b a := by
  by_cases hab : p.Rel a b
  · exact Or.inl hab
  · let q := p.comparisonExtension (p.maximal_addCancellative hm) (p.maximal_mulCancellative hm) a b hab
    have he : p ≤ q := fun _ _ h => ⟨0, by simpa only [zero_mul, add_zero] using h⟩
    have hba : q.Rel b a := ⟨1, by convert p.refl (a + b) using 1 <;> ring⟩
    exact Or.inr ((hm he) b a hba)

theorem exists_maximal (p : StrassenPreorder S) :
    ∃ q : StrassenPreorder S, p ≤ q ∧ IsMax q := by
  let Q := {q : StrassenPreorder S // p ≤ q}
  have hz : ∃ m : Q, IsMax m := zorn_le (by
    intro c hc
    by_cases hn : c.Nonempty
    · obtain ⟨q0, hq0⟩ := hn
      let R (a b : S) := ∃ q ∈ c, q.val.Rel a b
      have joint {a b u v : S} (h : R a b) (g : R u v) :
          ∃ q ∈ c, q.val.Rel a b ∧ q.val.Rel u v := by
        obtain ⟨q, hq, hab⟩ := h
        obtain ⟨r, hr, huv⟩ := g
        rcases hc.total hq hr with hqr | hrq
        · exact ⟨r, hr, hqr _ _ hab, huv⟩
        · exact ⟨q, hq, hab, hrq _ _ huv⟩
      let q : StrassenPreorder S := {
        Rel := R
        refl := fun a => ⟨q0, hq0, q0.val.refl a⟩
        trans := by
          intro a b u h g
          obtain ⟨r, hr, hab, hbu⟩ := joint h g
          exact ⟨r, hr, r.val.trans hab hbu⟩
        zero_le := fun a => ⟨q0, hq0, q0.val.zero_le a⟩
        nat_iff := fun m n => ⟨fun ⟨r, _, h⟩ => (r.val.nat_iff m n).mp h,
          fun h => ⟨q0, hq0, (q0.val.nat_iff m n).mpr h⟩⟩
        add := by
          intro a b u v h g
          obtain ⟨r, hr, hab, huv⟩ := joint h g
          exact ⟨r, hr, r.val.add hab huv⟩
        mul := by
          intro a b u v h g
          obtain ⟨r, hr, hab, huv⟩ := joint h g
          exact ⟨r, hr, r.val.mul hab huv⟩
        cofinal := by
          intro a b hb
          obtain ⟨n, hn⟩ := q0.val.cofinal a b hb
          exact ⟨n, q0, hq0, hn⟩ }
      have hpq : p ≤ q := fun a b h => ⟨q0, hq0, q0.prop a b h⟩
      exact ⟨⟨q, hpq⟩, fun r hr _ _ h => ⟨r, hr, h⟩⟩
    · exact ⟨⟨p, le_refl p⟩, fun r hr => False.elim (hn ⟨r, hr⟩)⟩)
  obtain ⟨m, hm⟩ := hz
  refine ⟨m.val, m.prop, ?_⟩
  intro q hmq
  exact hm (show m ≤ (⟨q, le_trans m.prop hmq⟩ : Q) from hmq)

end StrassenPreorder
end Lemmata.TensorRank.Spectrum
