---
title: An Explicit Bound on the Relativistic Correction to Schrödinger Kinetic Energy
---

```{include} ../_generated/provenance/schrodinger-remainder-bound.md
```

This entry isolates a conditional algebraic result from the public
LeanSchrodingerDerivation artifact. It begins with the positive relativistic
energy branch; it does not derive that mass shell, an arbitrary-wavefunction
position-space equation, Born's rule, or a complete quantum theory.

```{prf:theorem} Relativistic correction bound
:label: thm-schrodinger-remainder-bound

Let $m>0$ and $p\in\mathbb{R}$. Define

$$
E=\sqrt{m^2+p^2},\qquad
R=-\frac{p^4}{2m(E+m)^2}.
$$

Then the rest-energy-removed positive relativistic energy decomposes exactly as

$$
E-m=\frac{p^2}{2m}+R,
$$

and its correction satisfies

$$
|R|\leq\frac{p^4}{8m^3}.
$$
```

```{prf:proof} of [](#thm-schrodinger-remainder-bound)
:nonumber:

Rationalizing $E-m$ gives $p^2/(E+m)$. Rewriting this fraction around
$p^2/(2m)$ gives the displayed correction exactly. Since $E\geq m>0$, the
denominator of the correction is at least $8m^3$, which yields the bound.
```

```{literalinclude} ../../lean/Lemmata/SchrodingerRemainderBound/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/schrodinger-remainder-bound.md
```
