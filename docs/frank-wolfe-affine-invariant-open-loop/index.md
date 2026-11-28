---
title: "Affine-invariant accelerated rates for Frank–Wolfe with open-loop step-sizes"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-affine-invariant-open-loop.md
```

:::{note}
This entry formalizes the paper *Accelerated Affine-Invariant Convergence Rates of the Frank–Wolfe
Algorithm with Open-Loop Step-Sizes* by Elias Wirth, Javier Peña and Sebastian Pokutta
[@wirth2023accelerated], currently its measures of optimality and the rates under strong growth
(Section 3); numbers refer to the arXiv version.
:::

The Frank–Wolfe algorithm is affine invariant: an affine change of variables maps its iterates to
the iterates of the transformed problem. Its classical analysis is not, since smoothness, strong
convexity and diameters depend on a norm. The paper states its assumptions and its rates in terms of
quantities that do not depend on a norm: the Bregman divergence of the objective along the
Frank–Wolfe segment, the Frank–Wolfe gap $g_t = \langle \nabla f(x_t), x_t - v_t \rangle$ and the
primal gap. Under a *growth property* that bounds the Bregman divergence by a power of the
Frank–Wolfe gap, the open-loop step sizes $\eta_t = \ell/(t + \ell)$ converge at rates up to
$O(t^{-\ell})$, for the primal gap and also for duality gaps.

The statements hold in real normed spaces, for every Frank–Wolfe run, with any tie-breaking in the
linear minimization oracle; the step sizes are those of [Acceleration of Frank–Wolfe algorithms with
open-loop step-sizes](../frank-wolfe-open-loop-acceleration/index.md).

## Measures of optimality

```{prf:definition} Bregman divergence
:label: def-frank-wolfe-affine-invariant-open-loop-bregman
:nonumber:

$D_f(y, x) = f(y) - f(x) - \langle \nabla f(x), y - x \rangle$.
```

A Frank–Wolfe step changes the objective by exactly
$f(x_{t+1}) - f(x_t) = -\eta_t g_t + D_f(x_{t+1}, x_t)$.

```{prf:definition} Best duality gap
:label: def-frank-wolfe-affine-invariant-open-loop-pd
:nonumber:

For a run with Frank–Wolfe gaps $g_k$, the best duality gap is
$\mathrm{pd}_t = \min_{k \le t} \left( f(x_t) - f(x_k) + g_k \right)$.
```

By Fenchel duality, $\mathrm{pd}_t$ is the gap between the primal iterate $x_t$ and the best of the
dual iterates $\nabla f(x_k)$. It lies between the primal gap and the Frank–Wolfe gap,
$f(x_t) - f(x^\star) \le \mathrm{pd}_t \le g_t$, and the identity above gives
$\mathrm{pd}_{t+1} \le \mathrm{pd}_t - \eta_t g_t + D_f(x_{t+1}, x_t)$.

```{prf:definition} Smallest Frank–Wolfe gap
:label: def-frank-wolfe-affine-invariant-open-loop-min-gap
:nonumber:

$\min_{k \le t} g_k$, the smallest Frank–Wolfe gap among the first $t + 1$ iterations.
```

## Strong growth

```{prf:definition} Strong growth
:label: def-frank-wolfe-affine-invariant-open-loop-strong
:nonumber:

For $M > 0$ and $r \in [0, 1]$, $(C, f)$ has the *strong $(M, r)$-growth property* if
$D_f(x + \eta(v - x), x) \le \frac{M\eta^2}{2}\, g(x)^r$ for all $x \in C$, all Frank–Wolfe vertices
$v \in \operatorname{argmin}_{y \in C} \langle \nabla f(x), y \rangle$ and all $\eta \in [0, 1]$,
where $g(x) = \langle \nabla f(x), x - v \rangle$.
```

For $r = 0$ this is a slight relaxation of the curvature condition of Jaggi; it holds with $M = 4L$
when $f$ is $L$-smooth with respect to the norm whose unit ball is $(C - C)/2$, and with
$M = L\delta^2$ for $L$-smoothness in any norm and the diameter $\delta$ of $C$.

```{prf:theorem} Strong $(M, 0)$-growth
:label: thm-frank-wolfe-affine-invariant-open-loop-strong-zero
:enumerator: 3.1

Let $C$ be convex, $(C, f)$ with the strong $(M, 0)$-growth property, $M \ge 0$, and $\ell \ge 2$.
Every Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$ satisfies $\mathrm{pd}_t \le \eta_t M$ for all
$t \ge 1$.
```

Since $\mathrm{pd}_t \le g_t$, the basic recursion gives
$\mathrm{pd}_{t+1} \le (1 - \eta_t)\mathrm{pd}_t + \eta_t^2 M/2$, and
$(t + \ell)^2 \ge (t + \ell/2)(t + \ell + 1)$ closes the induction.

```{prf:lemma} Products of step sizes
:label: lem-frank-wolfe-affine-invariant-open-loop-product
:enumerator: 3.3

For $\ell \ge 1$ and $1 \le S \le t$, $\prod_{i=S}^{t} (1 - \eta_i) \le (\eta_t/\eta_{S-1})^\ell$.
```

The product is $S \cdots (S + \ell - 1)/((t + 1) \cdots (t + \ell))$; the formal proof goes by
induction on $t$ with Bernoulli's inequality.

```{prf:theorem} Strong $(M, 1)$-growth
:label: thm-frank-wolfe-affine-invariant-open-loop-strong-one
:enumerator: 3.2

Let $f$ be convex with a minimizer on $C$, $(C, f)$ with the strong $(M, 1)$-growth property,
$M > 0$, $\ell \ge 1$, and $S = \max\{1, \lceil \ell M/2 - \ell \rceil\}$. Every Frank–Wolfe run
with $\eta_t = \ell/(t + \ell)$ satisfies, for all $t \ge S$,

$$
\mathrm{pd}_t \le \mathrm{pd}_S \left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^\ell
\exp\left(\frac{M\ell^2}{2S}\right).
$$

Moreover, for $\varepsilon \in (0, 1)$, let $R_0$ be the larger of $S$ and
$\lceil \ell M/(2(1 - \varepsilon)) - \ell \rceil$. For all $t$ with
$e^{1/\ell}(R_0 + \ell) \le t + \ell$,

$$
\min_{k \le t} g_k \le \mathrm{pd}_S \left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^\ell
\frac{\exp\left(3 + M\ell^2/(2S)\right)}{\varepsilon}.
$$
```

From $S$ on, $\eta_t M/2 \le 1$, and strong $(M, 1)$-growth gives
$\mathrm{pd}_{t+1} \le (1 - \eta_t + \eta_t^2 M/2)\,\mathrm{pd}_t$. The product of the factors
$1 - \eta_i$ is bounded by Lemma 3.3, and that of the factors $1 + \eta_i^2 M/(2(1 - \eta_i))$ by
$\exp(M\ell^2/(2S))$. For the second claim, a stretch $R, \dots, t$ with
$\eta_i M/2 \le 1 - \varepsilon$ lowers $\mathrm{pd}$ by $\varepsilon \sum_i \eta_i g_i$, and
$\sum_{i=R}^{t} \eta_i \ge 1$ when $t + \ell \ge e^{1/\ell}(R + \ell)$.

```{prf:lemma} Products of step sizes with a margin
:label: lem-frank-wolfe-affine-invariant-open-loop-product-eps
:enumerator: 3.5

For $\ell \ge 1$, $1 \le S \le t$ and $\varepsilon \in [0, \ell]$,

$$
\prod_{i=S}^{t} \left(1 - \left(1 - \frac{\varepsilon}{\ell}\right)\eta_i\right) \le
\left(\frac{\eta_t}{\eta_{S-1}}\right)^{\ell-\varepsilon}
\exp\left(\frac{\varepsilon\ell}{S}\right).
$$
```

Each factor is $(1 - \eta_i)(1 + \varepsilon/i)$, and
$\sum_{i=S}^{t} 1/i \le \ell/S + \log((t + \ell)/(S - 1 + \ell))$.

```{prf:theorem} Strong $(M, r)$-growth, $r \in [0, 1)$
:label: thm-frank-wolfe-affine-invariant-open-loop-strong-r
:enumerator: 3.4

Let $f$ be convex with a minimizer on $C$, $(C, f)$ with the strong $(M, r)$-growth property,
$M > 0$, $r \in [0, 1)$, $\ell \ge 1$, $\varepsilon \in (0, \ell)$ and
$k = \min\{\ell - \varepsilon, 1/(1 - r)\}$. Every Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$
satisfies, for all $t \ge 1$,

$$
\mathrm{pd}_t \le e^{\varepsilon\ell} \max\left\{ \eta_{t-1}^{\ell-\varepsilon}\, \mathrm{pd}_1,\
\eta_{t-1}^{k} \left(\frac{\ell M}{2\varepsilon}\right)^{1/(1-r)} \right\},
$$

and, for all $t \ge \lceil e^{1/k}(1 + \ell) - \ell \rceil$,

$$
\min_{k' \le t} g_{k'} \le e^{3 + \varepsilon\ell} \eta_{t-1}^{k} \max\left\{ \mathrm{pd}_1,\
\left(\frac{\ell M}{2\varepsilon}\right)^{1/(1-r)} \right\}.
$$
```

With the threshold $T_i = (\eta_i \ell M/(2\varepsilon))^{1/(1-r)}$, a step whose Frank–Wolfe gap is
at most $T_i$ leaves $\mathrm{pd}_{i+1} \le T_i$, and every other step contracts $\mathrm{pd}$ by
$1 - (1 - \varepsilon/\ell)\eta_i$. So $\mathrm{pd}_t$ is at most the value at the start of its last
stretch of contracting steps times a product that Lemma 3.5 bounds.

:::{note}
**Differences from the paper.**
- The statements hold in real normed spaces, for every Frank–Wolfe run, with the Frank–Wolfe gaps of
  the run's atoms; $\ell$ is a natural number as in the paper. Theorem 3.1 needs no convexity.
- Theorem 3.4 has $\mathrm{pd}_1$ where the paper has $M/2$. The proof bounds
  $\mathrm{pd}_1 \le M/2$ as in Theorem 3.1, which needs strong $(M, 0)$-growth; strong
  $(M, r)$-growth only gives $\mathrm{pd}_1 \le (M/2) g_0^r$. Under strong $(M, 0)$-growth the two
  statements agree.
- In the second claim of Theorem 3.2, the threshold $e^{1/\ell}(R_0 + \ell) \le t + \ell$ replaces
  $t \ge \lceil e^{1/\ell} \ell M/(2(1 - \varepsilon)) - \ell + 1 \rceil$: the proof needs the index
  $R = \lfloor (t + \ell)/e^{1/\ell} - \ell \rfloor$ to satisfy $\eta_R M/2 \le 1 - \varepsilon$ and
  $R \ge S$, which the paper's threshold does not guarantee.
:::

## Coverage

This entry currently covers the measures of optimality and Section 3. The rates under weak and
(relaxed) gaps growth (Sections 4 and 5) and the sufficient conditions for the growth properties are
planned.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWAffineOpenLoop/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-affine-invariant-open-loop.md
```
