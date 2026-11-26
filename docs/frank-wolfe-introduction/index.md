---
title: "The Frank–Wolfe algorithm: a short introduction"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-introduction.md
```

The Frank–Wolfe algorithm [@frank1956algorithm] minimizes a smooth function over a compact
convex set $C$ using only a linear minimization oracle. Each step asks the oracle for the atom
$v_t \in \operatorname{argmin}_{v \in C} f'(x_t)(v)$ and moves toward it,
$x_{t+1} = x_t + \gamma_t (v_t - x_t)$. The paper formalized here is a short introduction to the
method and its baseline results. This entry covers Lemmas 4.1–4.3, Theorems 4.4 and 4.5,
Proposition 4.6, Theorem 4.7, Lemmas 4.9–4.11 and Theorem 5.1, in the paper's numbering. The
objects (oracle, iterates, step-size rules, gaps) are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md), and Lemmas 4.1 and 4.3 and Theorem 4.4 are
bound to the core's theorems. The statements of Section 4 hold in any real normed space;
Theorem 5.1 is about $\ell_p^n$.

:::{admonition} Errata
:class: warning

**Lemma 4.10.** The first case is stated "if $\gamma_t \in [0, 1]$", which always holds. Read
literally it includes the clipped step $\gamma_t = 1$, where the bound can fail: for a quadratic
with $L = M = 1$, $\|v - x\| = 1$ and $g = 10$, the decrease is $9.5$ while the bound claims
$(g^2 + a^2)/2 = 90.5$. The proof treats the unclipped step, and the formal statement assumes
$g/(M\|v - x\|^2) \le 1$.
:::

## Gaps and optimality

Three quantities measure how far $x \in C$ is from optimal. The *primal gap*
$f(x) - f(x^\star)$ is what we want to control. The *dual gap* $f'(x)(x - x^\star)$ dominates
it by convexity. The *Frank–Wolfe gap* $\max_{v \in C} f'(x)(x - v)$ dominates both, and unlike
them it is computable: the oracle's answer for $f'(x)$ attains the maximum.

```{prf:lemma} Primal gap, dual gap and Frank–Wolfe gap
:label: lem-frank-wolfe-introduction-gaps
:enumerator: 4.1

For a convex differentiable $f$, a minimizer $x^\star$ of $f$ on a compact set $C$ and $x \in C$:
$f(x) - f(x^\star) \le f'(x)(x - x^\star) \le \max_{v \in C} f'(x)(x - v)$.
```

The Frank–Wolfe gap is therefore a certificate: when it is small, so is the primal gap. It
vanishes exactly at the minimizers.

```{prf:lemma} First-order optimality
:label: lem-frank-wolfe-introduction-optimality
:enumerator: 4.2

Let $f$ be convex and differentiable and $C$ compact and convex. A point $x^\star \in C$
minimizes $f$ on $C$ if and only if $f'(x^\star)(x^\star - v) \le 0$ for all $v \in C$. In
particular the Frank–Wolfe gap at a minimizer is $0$.
```

## Convergence

Smoothness turns each step into guaranteed progress.

```{prf:lemma} Primal progress from smoothness
:label: lem-frank-wolfe-introduction-progress
:enumerator: 4.3

If $f$ is $L$-smooth, a step of length $\gamma$ from $x$ toward $v$ satisfies
$f(x) - f(x + \gamma (v - x)) \ge \gamma f'(x)(x - v) - \gamma^2 \tfrac{L}{2}\|v - x\|^2$.
```

With the Frank–Wolfe gap on the right-hand side, which is at least the primal gap, the primal
gap $h_t$ satisfies $h_{t+1} \le (1 - \gamma_t) h_t + \gamma_t^2 L D^2/2$, where $D$ is the
diameter of $C$. For $\gamma_t = 2/(t+2)$ this recursion gives the classical rate
[@jaggi2013revisiting].

```{prf:theorem} Primal convergence of the Frank–Wolfe algorithm
:label: thm-frank-wolfe-introduction-convergence
:enumerator: 4.4

Let $f$ be convex and $L$-smooth and $C$ compact and convex with diameter $D$. With the
step sizes $\gamma_t = 2/(t+2)$, $f(x_t) - f(x^\star) \le 2 L D^2 / (t+2)$ for all $t \ge 1$.
```

The Lean statement covers short steps and exact line search as well.

The Frank–Wolfe gap converges at the same rate. The iterates of the second half of the run,
from $k_0 = \lfloor (t+2)/2 \rfloor$ on, cannot all have a large gap. Each step decreases the primal
gap by about $\gamma_k g_k$, and the primal gap at $k_0$ is already at most $2LD^2/(k_0+2)$.

```{prf:theorem} Frank–Wolfe gap convergence of the Frank–Wolfe algorithm
:label: thm-frank-wolfe-introduction-gap
:enumerator: 4.5

Under the assumptions of Theorem 4.4, for every $t \ge 1$ the running minimum of the Frank–Wolfe
gaps satisfies
$\min_{0 \le \tau \le t} \max_{v \in C} f'(x_\tau)(x_\tau - v) \le 6.75\, L D^2/(t+2)$.
```

## A lower bound for any step sizes

The iterates are convex combinations of $x_1$ and the atoms. The weight of $x_1$ shrinks by the
factor $1 - \gamma_\tau$ in every step, but never vanishes unless some $\gamma_\tau = 1$. If the
gradient at the optimum points into the feasible region, this remaining weight keeps the primal
gap bounded below.

```{prf:proposition} A lower bound for any step sizes
:label: prop-frank-wolfe-introduction-lower
:enumerator: 4.6

Let $f$ be convex and $L$-smooth, and let the step sizes satisfy $\gamma_\tau \in [0, 1]$. Then
for every $t \ge 1$,
$f(x_t) - f(x^\star) \ge \prod_{\tau=1}^{t-1} (1 - \gamma_\tau) \cdot f'(x^\star)(x_1 - x^\star)$.
```

```{prf:proposition} The lower bound for the open-loop step sizes
:label: prop-frank-wolfe-introduction-lower-open-loop
:enumerator: 4.6

For $\gamma_\tau = 2/(\tau+2)$ the product telescopes, and
$f(x_t) - f(x^\star) \ge \frac{2}{t(t+1)} \, f'(x^\star)(x_1 - x^\star)$ for every $t \ge 1$.
```

So when $f'(x^\star)(x_1 - x^\star) > 0$, open-loop Frank–Wolfe cannot converge faster than
$1/t^2$, however favourable the function. The bound holds for every run, not only in the worst
case over instances, unlike the classical lower bounds [@lan2013complexity].

## Nonconvex objectives

Without convexity, the primal gap need not go to zero, but the Frank–Wolfe gap still measures
stationarity. Summing the progress lemma over the run with a constant step size controls its
smallest value.

```{prf:theorem} Convergence for nonconvex objectives
:label: thm-frank-wolfe-introduction-nonconvex
:enumerator: 4.7

Let $f$ be $L$-smooth, not necessarily convex, and $C$ compact and convex with diameter $D$. With
the constant step size $\gamma = 1/\sqrt{T+1}$, some iterate $x_t$ with $t \le T$ has
Frank–Wolfe gap at most $\max\{2 h_0, L D^2\} / \sqrt{T+1}$, where
$h_0 = f(x_0) - f(x^\star)$.
```

## Adaptive step sizes

The short step needs the smoothness constant $L$, which is rarely known. The adaptive strategy
works with an estimate $M$: it takes the short step for $M$ and accepts it if
$f'(x^+)(x - v) \ge 0$ at the new point $x^+$, otherwise it increases $M$. This test needs a
single gradient and no function values. The next lemmas show that the test certifies progress,
and that it always passes once $M = L$.

```{prf:lemma} Smoothness revisited
:label: lem-frank-wolfe-introduction-smoothness
:enumerator: 4.9

If $f$ is convex and $L$-smooth with $L > 0$, then for all $x, y$:
$\dfrac{\left((f'(y) - f'(x))(y - x)\right)^2}{2L\|y - x\|^2} \le f(y) - f(x) - f'(x)(y - x)$.
```

The paper assumes smoothness and convexity on a neighbourhood of $C$; the Lean statement assumes
them on the whole space. The proof goes through co-coercivity (Lemma 1.8 of
@braun2025conditional), $\|f'(y) - f'(x)\|^2 \le 2L(f(y) - f(x) - f'(x)(y - x))$, which holds in
any normed space.

```{prf:lemma} Primal progress from the adaptive test
:label: lem-frank-wolfe-introduction-adaptive-progress
:enumerator: 4.10

Let $f$ be convex and $L$-smooth, $g = f'(x)(x - v) \ge 0$, $d = \|v - x\| > 0$, $M > 0$,
$\gamma = \min\{g/(Md^2), 1\}$ and $x^+ = x + \gamma (v - x)$, and suppose
$a = f'(x^+)(x - v) \ge 0$. If $g/(Md^2) \le 1$, then
$f(x) - f(x^+) \ge (g^2 + a^2)/(2\max\{L, M\} d^2)$. If $\gamma = 1$ and $M \ge L$, then
$f(x) - f(x^+) \ge g/2 + a^2/(2g)$.
```

```{prf:lemma} Smoothness implies the adaptive test
:label: lem-frank-wolfe-introduction-adaptive-test
:enumerator: 4.11

If $f$ is $L$-smooth and $x^+$ is the short step from $x$ toward $v$ for the constant $L$, with
$f'(x)(x - v) \ge 0$, then $f'(x^+)(x - v) \ge 0$.
```

## Approximate Carathéodory

Carathéodory's theorem writes every point of the convex hull of $V \subseteq \mathbb{R}^n$ as a
convex combination of $n + 1$ points of $V$. Allowing an error $\varepsilon$ removes the dimension:
run Frank–Wolfe on $f(x) = \|x - x^*\|_p^2$ over the convex hull of $V$, with the oracle answering
points of $V$. After $t$ steps the iterate is a convex combination of at most $t + 1$ points of $V$,
and the convergence rate bounds its distance to $x^*$.

```{prf:theorem} Approximate Carathéodory
:label: thm-frank-wolfe-introduction-caratheodory
:enumerator: 5.1

Let $2 \le p < \infty$, let $V \subseteq \mathbb{R}^n$ be compact with $\ell_p$-diameter $D$, let
$x^*$ lie in the convex hull of $V$, and let $\varepsilon > 0$. There is a set $S \subseteq V$ of at
most $\lceil 4(p-1)D^2/\varepsilon^2 \rceil + 2$ points with a point $x$ in its convex hull such
that $\|x - x^*\|_p \le \varepsilon$.
```

The paper states the bound as $O(pD^2/\varepsilon^2)$; the formal statement makes the constant
explicit. The smoothness behind it is that $\|\cdot\|_p^2$ is $2(p-1)$-smooth with respect to the
$\ell_p$ norm. The proof bounds the second derivative of $t \mapsto \|a + tb\|_p^2$ by
$2(p-1)\|b\|_p^2$ using Hölder's inequality, after replacing $|x_i|^p$ by $(x_i^2 + \delta)^{p/2}$
to keep every term smooth, and then lets $\delta \to 0$.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfeIntro/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-introduction.md
```
