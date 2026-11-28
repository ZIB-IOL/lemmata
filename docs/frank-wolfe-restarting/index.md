---
title: "Restarting Frank–Wolfe under Hölderian error bounds"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-restarting.md
```

:::{note}
This entry formalizes results of the paper *Restarting Frank–Wolfe: Faster Rates Under Hölderian
Error Bounds* by Thomas Kerdreux, Alexandre d'Aspremont and Sebastian Pokutta
[@kerdreux2018restarting], currently the strong Wolfe gap bounds (Lemmas 2.3 and 3.6) and the rate
of vanilla Frank–Wolfe over strongly convex sets (Theorem 7.3); numbers refer to the arXiv version.
:::

The Frank–Wolfe algorithm converges at the rate $O(1/t)$ for smooth convex objectives, and its
away-step variant converges linearly over polytopes for strongly convex objectives. A
$(\theta, c)$-Hölderian error bound,
$\operatorname{dist}(x, X^\star) \le c\,(f(x) - f^\star)^\theta$ with $\theta \in [0, 1/2]$,
interpolates between the two: $\theta = 0$ is no information and $\theta = 1/2$ follows from strong
convexity. The paper restarts a fractional version of away-step Frank–Wolfe whenever a computable
optimality measure, the strong Wolfe gap, has dropped by a constant factor; this entry starts with
the properties of that measure.

## The strong Wolfe gap

For an iterate $x$ written as a convex combination of an active set $S$ of vertices, with an away
vertex $a \in \operatorname{argmax}_{y \in S} \langle \nabla f(x), y \rangle$ and a Frank–Wolfe
vertex $v \in \operatorname{argmin}_{z \in \mathcal{C}} \langle \nabla f(x), z \rangle$, the strong
Wolfe gap is $w(x, S) = \langle \nabla f(x), a - v \rangle$, the sum of the away gap
$\langle \nabla f(x), a - x \rangle$ and the Frank–Wolfe gap $\langle \nabla f(x), x - v \rangle$.

```{prf:lemma} The strong Wolfe gap
:label: lem-frank-wolfe-restarting-gap
:enumerator: 2.3

Let $x$ be a convex combination of $S \subseteq \mathcal{V}$ with positive weights, and let $f$ be
convex and differentiable over $\operatorname{conv}(\mathcal{V})$. Then
$f(x) - f^\star \le w(x, S)$, and $w(x, S) = 0$ if and only if $x$ minimizes $f$ over
$\operatorname{conv}(\mathcal{V})$.
```

At a minimizer the Frank–Wolfe gap vanishes, and so does the away gap: the terms
$\langle \nabla f(x), y - x \rangle$, $y \in S$, are nonnegative and their positive combination is
$0$.

```{prf:lemma} Strong Wolfe primal bound
:label: lem-frank-wolfe-restarting-heb
:enumerator: 3.6

Let $f$ be convex and differentiable over $\operatorname{conv}(\mathcal{V})$ with a
$(\theta, c)$-Hölderian error bound, and let $\delta > 0$ have the scaling property of the pyramidal
width. For $x \in \operatorname{conv}(S)$ with $S \subseteq \mathcal{V}$,

$$
f(x) - f^\star \le \Big(\frac{c}{\delta}\Big)^{1/(1-\theta)} w(x, S)^{1/(1-\theta)}.
$$
```

With a minimizer $x^\star$ near the distance from $x$ to $X^\star$, convexity gives
$f(x) - f^\star \le \langle \nabla f(x), x - x^\star \rangle$, the scaling property bounds this by
$w(x, S)\,\|x - x^\star\|/\delta$, and the error bound bounds $\|x - x^\star\|$ by
$c\,(f(x) - f^\star)^\theta$.

## Vanilla Frank–Wolfe over strongly convex sets

```{prf:theorem} Strongly convex sets
:label: thm-frank-wolfe-restarting-strongly-convex
:enumerator: 7.3

Let $\mathcal{C}$ be compact and $\alpha$-strongly convex with diameter $D > 0$, and let $f$ be
convex and $L$-smooth with a $(\theta, c)$-Hölderian error bound, $\theta \in (0, 1/2]$. With
$K = (Lc/\alpha)^{1/(1-\theta)}$ and $t_0 = \max\{\lfloor \log_{1/2}(2K/(LD^2)) \rfloor + 2, 1\}$,
every run of Frank–Wolfe with short steps satisfies $f(x_t) - f^\star \le (LD^2/2)\,2^{1-t}$ for
$1 \le t < t_0$ and $f(x_t) - f^\star \le K/(1 + (1 - \theta)(t - t_0)/2)^{1/(1-\theta)}$ for
$t \ge t_0$, the rate $O(t^{-1/(1-\theta)})$.
```

This is the case $q = 2$ of Theorem 2.10 of [Frank–Wolfe over uniformly convex
sets](../frank-wolfe-uniformly-convex-sets/index.md), and the formal proof is that theorem.

:::{note}
**Differences from the paper.**
- The statements hold in real normed spaces.
- Lemmas 2.3 and 3.6 are stated for a given active set $S$ with the gap $w(x, S)$. Since Lemma 3.6
  holds for every active set of $x$, it gives the paper's bound with $w(x) = \min_S w(x, S)$. The
  scaling property is that of the away-step entry, which the pyramidal width satisfies (Lemma 3.4 of
  the paper).
- Theorem 7.3 is stated with explicit constants; its recursion constant $(\alpha/c)/(2L)$ improves
  the paper's $\alpha/(8Lc)$. The case $\theta = 0$ is the classical rate.
:::

## Coverage

This entry covers Lemmas 2.3 and 3.6 and Theorem 7.3. Not covered yet are the fractional away-step
Frank–Wolfe algorithm and its complexity (Algorithm 1, Propositions 4.1 and 4.2), the restart
schemes (Theorem 5.1, Corollary 5.2, Proposition 5.3), the Hölder smooth versions (Section 6), the
fractional Frank–Wolfe algorithm (Section 7) and the experiments.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWRestart/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-restarting.md
```
