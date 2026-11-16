---
title: Isotropy and Finite-Spacing Error of the C19 Cubic Symbol
---

```{include} ../_generated/provenance/c19-isotropic-symbol.md
```

This entry isolates the spatial-symbol calculation from the public
LeanKleinGordonDerivation artifact. It concerns a stated C19 stencil and its
long-wave expansion. It does not prove convergence of arbitrary nonlinear
lattice trajectories, a physical particle, or that the lattice models nature.

```{prf:theorem} C19 isotropic symbol and quartic error
:label: thm-c19-isotropic-symbol

For the positive-half C19 bonds consisting of three face directions of weight
two and six edge directions of weight one, the quadratic moment is exactly
isotropic with coefficient 12. For every real scale $h$ and wave vector $k$,
the full cosine symbol differs from its quadratic approximation by at most
$h^4$ times the explicitly defined weighted fourth moment.
```

```{prf:proof} of [](#thm-c19-isotropic-symbol)
:nonumber:

The finite list of weighted bonds gives the isotropic second moment by direct
algebra. Applying the centered cosine remainder bound to each bond and summing
with nonnegative weights yields the fourth-order estimate.
```

```{literalinclude} ../../lean/Lemmata/C19IsotropicSymbol/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/c19-isotropic-symbol.md
```
