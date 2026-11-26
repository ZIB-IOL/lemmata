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
method and its baseline results. This entry covers Lemmas 4.1–4.3, Theorem 4.4,
Proposition 4.6 and Theorem 4.7, in the paper's numbering. The objects (oracle, iterates,
step-size rules, gaps) are those of [Frank–Wolfe: the core](../frank-wolfe-core/index.md), and
Lemmas 4.1 and 4.3 and Theorem 4.4 are bound to the core's theorems. The statements hold in any
real normed space.

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

## Not yet covered

Theorem 4.5 (the running minimum of the Frank–Wolfe gaps is at most $6.75\,LD^2/(t+2)$), the
adaptive step sizes of Lemmas 4.9–4.11, and the approximate Carathéodory theorem
(Theorem 5.1) are planned for a later version of this entry; see @braun2025conditional for the
broader picture.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfeIntro/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-introduction.md
```
