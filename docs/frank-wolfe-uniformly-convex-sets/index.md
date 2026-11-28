---
title: "Frank–Wolfe over uniformly convex sets"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-uniformly-convex-sets.md
```

:::{note}
This entry formalizes results of the paper *Projection-Free Optimization on Uniformly Convex Sets*
by Thomas Kerdreux, Alexandre d'Aspremont and Sebastian Pokutta [@kerdreux2020projection], currently
the local scaling inequality (Lemma 2.4 and Corollary 2.8) and the rates under a Hölderian error
bound (Lemma 2.9 and Theorem 2.10); numbers refer to the arXiv version.
:::

The Frank–Wolfe algorithm converges at the rate $O(1/t)$ in general, linearly over polytopes with
away steps, and at the rate $O(1/t^2)$ over strongly convex sets. A set $\mathcal{C}$ is
$(\alpha, q)$-uniformly convex if
$\eta x + (1 - \eta) y + \eta(1 - \eta)\alpha\|x - y\|^q z \in \mathcal{C}$ for all
$x, y \in \mathcal{C}$, $\eta \in [0, 1]$ and unit vectors $z$. For $q = 2$ these are the strongly
convex sets, and the $\ell_p$-balls with $p > 2$ are uniformly convex but not strongly convex. The
paper shows that uniform convexity interpolates between the regimes. Its global results, the scaling
inequality $\alpha\|\nabla f(x)\|\,\|x - v\|^q \le \langle \nabla f(x), x - v \rangle$ for a
Frank–Wolfe vertex $v$ (Lemma 2.1) and the rates when the gradient is bounded away from zero
(Theorem 2.2), are Proposition 2.19 and Theorem 2.20 of [Conditional gradient methods: smoothness,
scaling and linear rates](../conditional-gradient-basics/index.md). This entry formalizes results
that go beyond them.

## Local uniform convexity

The rates only need the scaling inequality at the minimizer $x^\star$, with the gradient there.

```{prf:definition} Local uniform convexity
:label: def-frank-wolfe-uniformly-convex-sets-local-uc
:nonumber:

$\mathcal{C}$ is locally $(\alpha, q)$-uniformly convex at $x^\star$ if
$\eta x^\star + (1 - \eta) x + \eta(1 - \eta)\alpha\|x^\star - x\|^q z \in \mathcal{C}$ for all
$x \in \mathcal{C}$, $\eta \in [0, 1]$ and unit vectors $z$.
```

```{prf:definition} The local scaling inequality
:label: def-frank-wolfe-uniformly-convex-sets-local-scaling
:nonumber:

The local scaling inequality holds at $x^\star$ with parameters $(\alpha, q)$ if, for all
$x \in \mathcal{C}$,

$$
\frac{\alpha}{2}\|\nabla f(x^\star)\|\,\|x^\star - x\|^q \le \langle \nabla f(x^\star), x - x^\star
\rangle.
$$
```

```{prf:lemma} Local uniform convexity gives the local scaling inequality
:label: lem-frank-wolfe-uniformly-convex-sets-local-uc
:enumerator: 2.4

If $x^\star \in \mathcal{C}$ satisfies the first-order optimality condition
$\langle \nabla f(x^\star), x - x^\star \rangle \ge 0$ for $x \in \mathcal{C}$, and $\mathcal{C}$ is
locally $(\alpha, q)$-uniformly convex at $x^\star$, then the local scaling inequality holds at
$x^\star$.
```

The midpoint of $x^\star$ and $x$, moved by $\frac{\alpha}{4}\|x^\star - x\|^q$ in any unit
direction $z$, stays in $\mathcal{C}$. Optimality at $x^\star$ against these points, for directions
$z$ that nearly attain $\|\nabla f(x^\star)\|$, gives the inequality.

```{prf:corollary} A uniformly convex superset
:label: cor-frank-wolfe-uniformly-convex-sets-superset
:enumerator: 2.8

If $\mathcal{C} \subseteq \Gamma$ for an $(\alpha, q)$-uniformly convex set $\Gamma$, and
$x^\star \in \mathcal{C}$ satisfies $\langle \nabla f(x^\star), y - x^\star \rangle \ge 0$ for all
$y \in \Gamma$, that is, $-\nabla f(x^\star)$ lies in the normal cone of $\Gamma$ at $x^\star$, then
the local scaling inequality holds at $x^\star$ for $\mathcal{C}$.
```

So a set that is not uniformly convex, such as a polytope inscribed in a ball, still has the local
scaling inequality at minimizers where the gradient points into the ball's normal cone.

## Hölderian error bounds

A $(\mu, \theta)$-Hölderian error bound,
$\operatorname{dist}(x, \Omega^\star) \le \mu (f(x) - f^\star)^\theta$ on $\mathcal{C}$ for the set
$\Omega^\star$ of minimizers, replaces the lower bound on the gradient.

```{prf:lemma} Scaling under a Hölderian error bound
:label: lem-frank-wolfe-uniformly-convex-sets-heb-scaling
:enumerator: 2.9

Let $\mathcal{C}$ be $(\alpha, q)$-uniformly convex with $\alpha > 0$, and let $f$ be convex with a
$(\mu, \theta)$-Hölderian error bound, $\theta \in [0, 1/2]$. For $x \in \mathcal{C}$ and a
Frank–Wolfe vertex $v$,
$\frac{\alpha}{\mu}\|x - v\|^q (f(x) - f^\star)^{1-\theta} \le \langle \nabla f(x), x - v \rangle$.
```

Convexity and the error bound give

$$
f(x) - f^\star \le \|\nabla f(x)\|\,\operatorname{dist}(x, \Omega^\star) \le
\mu\|\nabla f(x)\|(f(x) - f^\star)^\theta,
$$

so $(f(x) - f^\star)^{1-\theta} \le \mu\|\nabla f(x)\|$, and the scaling inequality of Lemma 2.1
finishes the proof.

```{prf:theorem} Rates under a Hölderian error bound
:label: thm-frank-wolfe-uniformly-convex-sets-heb-rate
:enumerator: 2.10

Let $\mathcal{C}$ be compact, convex and $(\alpha, q)$-uniformly convex with $q \ge 2$ and diameter
$D > 0$, and let $f$ be convex and $L$-smooth with a $(\mu, \theta)$-Hölderian error bound,
$\theta \in (0, 1/2]$. With $a = 1 - 2\theta/q$, $K = (L(\mu/\alpha)^{2/q})^{1/a}$ and
$t_0 = \max\{\lfloor \log_{1/2}(2K/(LD^2)) \rfloor + 2, 1\}$, every run of Frank–Wolfe with short
steps satisfies $f(x_t) - f^\star \le (LD^2/2)\,2^{1-t}$ for $1 \le t < t_0$ and

$$
f(x_t) - f^\star \le \frac{K}{(1 + a(t - t_0)/2)^{1/a}} \quad \text{for } t \ge t_0,
$$

the rate $O(t^{-1/(1-2\theta/q)})$. For $q = 2$ and $\theta = 1/2$ this is the rate $O(1/t^2)$ of
Garber and Hazan.
```

With Lemma 2.9, the short step makes progress
$h_t \min\{1/2, (\alpha/\mu)^{2/q} h_t^{1-2\theta/q}/(2L)\}$, and the contraction lemma of the
basics entry (Lemma 2.21) turns this recursion into the rate.

:::{note}
**Differences from the paper.**
- The statements hold in real normed spaces; the paper works in $\mathbb{R}^d$.
- Lemma 2.4 assumes the first-order optimality condition at $x^\star$. Corollary 2.8 assumes only
  that $-\nabla f(x^\star)$ lies in the normal cone of $\Gamma$ at $x^\star$, which is what its
  proof uses; the paper also assumes $N_\Gamma(x^\star) \subseteq N_{\mathcal{C}}(x^\star)$ and that
  $\Gamma$ is compact.
- Lemma 2.9 does not need strict convexity of $f$: the error bound is stated with the distance to
  the set of minimizers.
- Theorem 2.10 is stated with the constants of the contraction lemma of the basics entry instead of
  Lemma A.1, and assumes $D > 0$.
:::

## Coverage

This entry covers Lemmas 2.4 and 2.9, Corollary 2.8 and Theorem 2.10; Lemma 2.1 and Theorem 2.2 are
Proposition 2.19 and Theorem 2.20 of the basics entry. Not covered yet are the rates under the local
scaling inequality (Lemma 2.7 and Theorem 2.5), online learning with linear oracles (Section 3), the
examples of uniformly convex sets (Section 4 and Appendix D) and the experiments.


## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWUniformlyConvex/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-uniformly-convex-sets.md
```
