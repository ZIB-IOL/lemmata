---
title: A cubical first-order factorization of the C19 continuum symbol
---

```{include} ../_generated/provenance/cubical-c19-factorization.md
```

Label the eight corners of a cube by three binary coordinates. Crossing one
coordinate direction flips one bit. Cubical orientation supplies a sign to
each crossing, while the parity of all three bits supplies a fourth grading.
These operations are defined explicitly on the eight corner amplitudes; no
matrices are assumed as input.

```{prf:theorem} Cubical C19 factorization
:label: thm-cubical-c19-factorization

Let $D(m,p)$ be the first-order operator made from the three signed cube
crossings, the corner-parity grading, a complex rest coefficient $m$, and a
real three-momentum $p$. With the continuum speed fixed by the C19 second
moment, its square is

$$
D(m,p)^2 = \left(m^2 + 12\left(p_0^2+p_1^2+p_2^2\right)\right)I.
$$
```

```{prf:proof} of [](#thm-cubical-c19-factorization)
:nonumber:
Each signed crossing performed twice returns to the same corner. Crossings in
different directions cancel in pairs because their orientation signs are
opposite around a square face. The even/odd corner grading likewise cancels
the mixed terms between the rest coefficient and each crossing. What remains
is one square from each of the three directions and the rest square. Finally,
the C19 continuum scale squares to $12$. Lean checks the corner cases and the
remaining ring identity.
```

```{literalinclude} ../../lean/Lemmata/CubicalC19Factorization/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

This is an exact algebraic factorization of the **continuum quadratic symbol**
associated with C19's second moment. It does not assert that the signed
crossings are native forces in a lattice action, that the full finite-spacing
C19 symbol is exactly factorized, or that a localized electron or physical
spin state has been derived.

```{prf:theorem} Exhaustive two-flavor classification
:label: thm-cubical-c19-factorization-two-flavor

The eight complex corner amplitudes split uniquely into the positive and
negative eigenspaces of a second involution made only from cube flips and
orientation signs. Their intersection contains only the zero amplitude, and
the cubical C19 first-order symbol preserves each sector.
```

```{prf:proof} of [](#thm-cubical-c19-factorization-two-flavor)
:nonumber:
The positive and negative projections are obtained by adding or subtracting
the geometric involution and dividing by two. Expanding the eight corners
shows that the involution squares to the identity, the two projections add
back to the original amplitude, and simultaneous membership forces every
corner amplitude to vanish. A second finite corner check proves that the
involution commutes with the cubical C19 symbol, so both sectors are invariant.
```

This theorem classifies the complete eight-corner algebraic fiber. It does not
assert that a measurement selects one sector or that the sectors are two
independently localized particles.

```{include} ../_generated/verification/cubical-c19-factorization.md
```
