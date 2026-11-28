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
the local scaling inequality and the rates it gives (Lemmas 2.4 and 2.7, Corollary 2.8 and Theorem
2.5, corrected), the rates under a Hölderian error bound (Lemma 2.9 and Theorem 2.10) and the regret
of follow the leader (Lemma 3.2 and Theorem 3.1); numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Theorems 2.2 and 2.5, case $q = 2$.** Both state $f(x_T) - f(x^\star) \le (1 - \rho)^T h_0$ with
$\rho = \max\{1/2, 1 - c\alpha/L\}$, a contraction by $\min\{1/2, c\alpha/L\}$ in every iteration.
This is false for the short step. The Euclidean unit disk is $(1/2, 2)$-uniformly convex; take
$f(x) = -x_2$, so $c = 1$, with $L = 10$ and $x_0 = (0, -1)$. The first short step has
$v_0 = (0, 1)$, gap $g_0 = 2$ and step size $\min\{1, g_0/(L\|x_0 - v_0\|^2)\} = 1/20$, so
$x_1 = (0, -0.9)$ and $h_1 = 1.9$, while the bound gives $(1 - 0.95) \cdot 2 = 0.1$. The intended
bound is $\rho^T h_0$. For Theorem 2.2 the corrected statement, with the factor
$\max\{1/2, 1 - \alpha c/(2L)\}$, is Theorem 2.20 of the basics entry. For Theorem 2.5 the proof
gives the factor $\max\{1/2, 1 - 1/(2LH^2)\}$ with the constant $H$ of Lemma 2.7, which is the
version formalized here.
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

## Rates under the local scaling inequality

When the scaling inequality holds only at $x^\star$, the distance between an iterate and its
Frank–Wolfe vertex is still controlled by the primal gap.

```{prf:lemma} Distance to the Frank–Wolfe vertex
:label: lem-frank-wolfe-uniformly-convex-sets-vertex-distance
:enumerator: 2.7

Let $f$ be convex with an $L$-Lipschitz gradient and $\|\nabla f\| \ge c > 0$ on $\mathcal{C}$, and
let the local scaling inequality hold at $x^\star \in \mathcal{C}$ with $\alpha > 0$ and $q \ge 2$.
For $x \in \mathcal{C}$ with $f(x) - f(x^\star) \le 1$ and a Frank–Wolfe vertex $v$ of $x$,
$\|x - v\| \le H (f(x) - f(x^\star))^{1/(q(q-1))}$ with
$H = 2\max\{(2L/(c\alpha))^{1/(q-1)}(2/(c\alpha))^{1/(q(q-1))}, (2/(c\alpha))^{1/q}\}$.
```

The local scaling inequality at $x$ with convexity gives
$\frac{c\alpha}{2}\|x - x^\star\|^q \le f(x) - f(x^\star)$. At $v$, the optimality of $v$ and the
Lipschitz gradient give $\frac{c\alpha}{2}\|v - x^\star\|^q \le L\|x - x^\star\|\,\|v - x^\star\|$.

```{prf:theorem} Rates under the local scaling inequality, corrected
:label: thm-frank-wolfe-uniformly-convex-sets-local-rate
:enumerator: 2.5

Let $\mathcal{C}$ be compact and convex, let $f$ be convex and $L$-smooth with
$\|\nabla f\| \ge c > 0$ on $\mathcal{C}$, and let the local scaling inequality hold at the
minimizer $x^\star$ with $\alpha > 0$ and $q \ge 2$. Let $H$ be the constant of Lemma 2.7 and
$a = 1 - 2/(q(q-1))$. If $f(x_S) - f(x^\star) \le 1$, every run of Frank–Wolfe with short steps
satisfies $h_{t+1} \le h_t \max\{1/2, 1 - h_t^a/(2LH^2)\}$ for $t \ge S$. For $q = 2$ the
convergence is therefore linear with factor $\max\{1/2, 1 - 1/(2LH^2)\}$, and for $q > 2$ the
contraction lemma gives the rate $O(t^{-1/(1 - 2/(q(q-1)))})$ with explicit constants.
```

By Lemma 2.7, $H^{-q(q-1)}\|x_t - v_t\|^{q(q-1)} \le h_t \le g_t$, a scaling inequality with
exponent $q(q-1)$, so the progress estimate behind Theorem 2.10 applies with this exponent. The rate
is slower than the global rate $O(t^{-1/(1-2/q)})$ of Theorem 2.2; whether the local inequality
gives the global rate is an open question of the paper.

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

## Online linear optimization

In online linear optimization, a learner picks $x_t \in \mathcal{C}$ and then observes a linear loss
$c_t$; follow the leader picks a minimizer of $c_1 + \dots + c_{t-1}$ over $\mathcal{C}$. Its regret
can be linear in general, but uniform convexity makes the leader stable.

```{prf:lemma} Stability of linear maximizers
:label: lem-frank-wolfe-uniformly-convex-sets-stability
:enumerator: 3.2

Let $\mathcal{C}$ be $(\alpha, q)$-uniformly convex with $\alpha > 0$ and $q \ge 2$, let
$\phi_1, \phi_2$ be linear functionals, not both zero, and let $v_i \in \mathcal{C}$ maximize
$\phi_i$ over $\mathcal{C}$. Then

$$
\langle \phi_1, v_1 - v_2 \rangle \le \left(\frac{1}{\alpha}\right)^{1/(q-1)}
\frac{\|\phi_1 - \phi_2\|^{1 + 1/(q-1)}}{\max\{\|\phi_1\|, \|\phi_2\|\}^{1/(q-1)}}.
$$
```

The scaling inequality at $v_1$ and at $v_2$ gives

$$
\alpha \max\{\|\phi_1\|, \|\phi_2\|\}\,\|v_1 - v_2\|^q
\le \langle \phi_1 - \phi_2, v_1 - v_2 \rangle \le \|\phi_1 - \phi_2\|\,\|v_1 - v_2\|,
$$

which bounds $\|v_1 - v_2\|$.

```{prf:definition} Follow the leader
:label: def-frank-wolfe-uniformly-convex-sets-ftl
:nonumber:

For losses $c_1, c_2, \dots$, follow the leader picks, for $t \ge 1$, some $x_t \in \mathcal{C}$
minimizing $c_1 + \dots + c_{t-1}$ over $\mathcal{C}$.
```

```{prf:theorem} Regret of follow the leader
:label: thm-frank-wolfe-uniformly-convex-sets-ftl
:enumerator: 3.1

Let $\mathcal{C}$ be $(\alpha, q)$-uniformly convex with $\alpha > 0$ and $q \ge 2$, let
$\|c_t\| \le M$, and let the averages $(c_1 + \dots + c_t)/t$ have norm at least $L_T > 0$ for
$1 \le t \le T$. The regret $\sum_{t \le T} \langle c_t, x_t - u \rangle$ of follow the leader
against every $u \in \mathcal{C}$ is at most
$2M(2M/(\alpha L_T))^{1/(q-1)} \frac{q-1}{q-2} T^{1 - 1/(q-1)}$ for $q > 2$, and
$\frac{4M^2}{\alpha L_T}(1 + \log T)$ for $q = 2$.
```

The regret equals $\sum_{t \le T} t\,\langle \nabla F_t, x_t - x_{t+1} \rangle$ for the averages
$\nabla F_t$; consecutive averages differ by at most $2M/t$, so Lemma 3.2 bounds each term by
$2M(2M/(\alpha L_T))^{1/(q-1)} t^{-1/(q-1)}$, and the sum of $t^{-1/(q-1)}$ is bounded by an
integral.

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
- Lemma 3.2 is proved from the scaling inequality at both maximizers, without the limits
  $\gamma \to 0, 1$ of the paper's argument, and only needs one of the functionals to be nonzero. In
  Theorem 3.1 the regret is against every comparator in $\mathcal{C}$, and the sum of $t^{-1/(q-1)}$
  is bounded by $\frac{q-1}{q-2}T^{1-1/(q-1)}$ through the integral from $1$.
- Theorem 2.5 is stated from an iteration $S$ with $f(x_S) - f(x^\star) \le 1$, the burn-in that
  Lemma 2.7 needs, and with the constants of the contraction lemma of the basics entry; for $q = 2$
  see the errata.
:::

## Coverage

This entry covers Lemmas 2.4, 2.7, 2.9 and 3.2, Corollary 2.8 and Theorems 2.5, 2.10 and 3.1; Lemma
2.1 and Theorem 2.2 are Proposition 2.19 and Theorem 2.20 of the basics entry. Not covered yet are
the examples of uniformly convex sets (Section 4 and Appendix D) and the experiments.


## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWUniformlyConvex/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-uniformly-convex-sets.md
```
