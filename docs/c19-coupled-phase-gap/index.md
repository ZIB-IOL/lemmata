---
title: A Positive Propagating Gap for a Coupled C19 Phase Branch
---

```{include} ../_generated/provenance/c19-coupled-phase-gap.md
```

This entry isolates one conditional spectral result from the public
LeanRedShiftDerivation artifact. It concerns the declared branch only; it does
not establish formation, nonlinear stability, a physical photon, gravity, or
observational agreement.

```{prf:theorem} Coupled C19 phase gap
:label: thm-c19-coupled-phase-gap

Let

$$
S(k_0,k_1,k_2)=8\sum_a(1-\cos k_a)
+8\sum_{a<b}(1-\cos k_a\cos k_b).
$$

For nonzero real radii $r_\Psi$ and $r_\chi$, if $S(k_0,k_1,k_2)>0$, then

$$
\left(\frac{r_\Psi^2r_\chi^2}{19^2}S(k_0,k_1,k_2)\right)
\left(\frac{1}{r_\Psi^2}+\frac{1}{1197r_\chi^2}\right)>0.
$$
```

```{prf:proof} of [](#thm-c19-coupled-phase-gap)
:nonumber:

The squares of both nonzero radii are positive. The scale factors $19^2$ and
$1197$ are positive, so the stiffness and both reciprocal contributions are
positive. Their product is therefore positive.
```

```{literalinclude} ../../lean/Lemmata/C19CoupledPhaseGap/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/c19-coupled-phase-gap.md
```
