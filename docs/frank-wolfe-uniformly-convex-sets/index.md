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
2.5, corrected), the rates under a Hölderian error bound (Lemma 2.9 and Theorem 2.10) the regret of
follow the leader (Lemma 3.2 and Theorem 3.1) and the examples of uniformly convex sets (Lemma 4.2
and Lemmas D.2 and D.3, corrected); numbers refer to the arXiv version.
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

**Lemmas D.2 and D.3.** Lemma D.2 states that the sublevel set $\{f \le w\}$ of a nonnegative
$L$-smooth $(\mu, r)$-uniformly convex function is $(\mu/\sqrt{2wL}, r)$-uniformly convex, and Lemma
D.3 that the ball of radius $\rho$ of a norm with $(\mu, s)$-uniformly convex square is
$(\mu/(2\rho), s)$-uniformly convex. Their proofs give half these constants, $\mu/(2\sqrt{2wL})$ and
$\mu/(4\rho)$, and the printed ones are false. For $f = \|x\|^2/2$ on the Euclidean plane, with
$\mu = L = 1$ and $w = 1/2$, and for the Euclidean norm, with $\mu = 2$ and $\rho = 1$, both lemmas
claim that the unit disk is $(1, 2)$-uniformly convex. But $x = (3/5, 4/5)$, $y = (3/5, -4/5)$ and
$\eta = 1/2$ give the point $(31/25, 0)$ outside the disk. The corrected constants are the best
possible here, since the disk is $(1/2, 2)$-uniformly convex.
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

## Examples of uniformly convex sets

The norm balls of uniformly convex spaces are the main examples. The modulus of convexity of a
normed space is
$\delta(\varepsilon) = \inf\{1 - \|(x + y)/2\| : \|x\|, \|y\| \le 1, \|x - y\| \ge \varepsilon\}$.

```{prf:definition} Modulus of convexity
:label: def-frank-wolfe-uniformly-convex-sets-modulus
:enumerator: 4.1

The modulus of convexity of a real normed space is the function $\delta$ above, with the infimum
over pairs of points of the closed unit ball.
```

```{prf:lemma} Unit balls of uniformly convex spaces
:label: lem-frank-wolfe-uniformly-convex-sets-ball
:enumerator: 4.2

If $\delta(\varepsilon) \ge \alpha\varepsilon^q$ for $\varepsilon \in [0, 2]$ with $\alpha \ge 0$,
the closed unit ball is $(\alpha, q)$-uniformly convex. If the closed unit ball is
$(\alpha, q)$-uniformly convex, the ball of radius $r > 0$ is $(\alpha/r^{q-1}, q)$-uniformly
convex.
```

For $\eta \le 1/2$, the point $\eta x + (1 - \eta) y$ is a convex combination of the midpoint, whose
norm is at most $1 - \delta(\|x - y\|)$, and of $y$; so its norm is at most
$1 - 2\eta\,\delta(\|x - y\|)$, which leaves room for the shift $\eta(1 - \eta)\alpha\|x - y\|^q$.

Sublevel sets of uniformly convex functions are a second source. A function is $(\mu, r)$-uniformly
convex if $f(y) \ge f(x) + \langle \nabla f(x), y - x \rangle + \frac{\mu}{2}\|x - y\|^r$ for all
$x, y$.

```{prf:proposition} Smoothness caps the exponent
:label: prop-frank-wolfe-uniformly-convex-sets-exponent
:nonumber:

On a real normed space with a nonzero vector, no $L$-smooth function is $(\mu, r)$-uniformly convex
with $\mu > 0$ and $r > 2$.
```

Along a line, uniform convexity bounds the Bregman distance below by $\frac{\mu}{2}t^r$ and
smoothness bounds it above by $\frac{L}{2}t^2$, which fails for large $t$ when $r > 2$.

```{prf:lemma} Sublevel sets, corrected
:label: lem-frank-wolfe-uniformly-convex-sets-sublevel
:enumerator: D.2

Let $f \ge 0$ be $L$-smooth with $L > 0$ and $(\mu, r)$-uniformly convex with $\mu > 0$ and
$r \ge 2$. For $w > 0$, the sublevel set $\{f \le w\}$ is $(\mu/(2\sqrt{2wL}), r)$-uniformly convex.
```

By the proposition, $r = 2$. At $z = \eta x + (1 - \eta) y$, uniform convexity gives
$f(z) \le w - \frac{\mu}{2}\eta(1 - \eta)\|x - y\|^2$; smoothness and $\|\nabla f(z)\|^2 \le 2Lf(z)$
give $f(z + u) \le (\sqrt{f(z)} + \sqrt{L/2}\,\|u\|)^2$, and concavity of the square root leaves
room for $\|u\| = \eta(1 - \eta)\frac{\mu}{2\sqrt{2wL}}\|x - y\|^2$.

```{prf:lemma} Norm balls, corrected
:label: lem-frank-wolfe-uniformly-convex-sets-norm-ball
:enumerator: D.3

If $x \mapsto \|x\|^2$ is $(\mu, s)$-uniformly convex with $\mu > 0$ and $s \ge 2$, the ball of
radius $\rho > 0$ is $(\mu/(4\rho), s)$-uniformly convex.
```

Here $s = 2$ by homogeneity, and the triangle inequality replaces smoothness in the argument for
Lemma D.2.

```{prf:proposition} The Euclidean disk
:label: prop-frank-wolfe-uniformly-convex-sets-disk
:nonumber:

The closed Euclidean unit disk is not $(1, 2)$-uniformly convex.
```

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
- Lemma 4.2 is stated for moduli of convexity of power type,
  $\delta(\varepsilon) \ge \alpha\varepsilon^q$ on $[0, 2]$, the case used in the paper; the formal
  modulus is $0$ when its defining set is empty.
- In Lemmas D.2 and D.3 the constants are those of the proofs (see the errata), and for exponents
  above $2$ the hypotheses cannot hold on a nontrivial space, so these lemmas are about $r = s = 2$.
  Lemma D.3 assumes uniform convexity of the square of the norm with its derivative, on any real
  normed space; the paper uses a finite-dimensional space.
:::

## Coverage

This entry covers Lemmas 2.4, 2.7, 2.9, 3.2 and 4.2, Corollary 2.8, Theorems 2.5, 2.10 and 3.1, and
Lemmas D.2 and D.3; Lemma 2.1 and Theorem 2.2 are Proposition 2.19 and Theorem 2.20 of the basics
entry. Not covered are the sharp moduli of convexity of $\ell_p$, $L_p$ and Schatten spaces that
Section 4 cites, Lemma B.1 on gauges, and the experiments.


## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWUniformlyConvex/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-uniformly-convex-sets.md
```
