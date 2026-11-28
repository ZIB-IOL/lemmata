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
[@wirth2023accelerated], its measures of optimality, its convergence rates (Sections 3 to 5) and its
sufficient conditions for the growth properties; numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Lemma 2.10, second part.** For $p \ge 2$, a function that is $L$-smooth with respect to
$\|\cdot\|_2$ is $L n^{1-2/p}$-smooth with respect to $\|\cdot\|_p$, since
$\|x\|_2 \le n^{1/2-1/p} \|x\|_p$ enters squared; the lemma states $L n^{1/2-1/p}$. For
$f(x) = \frac{L}{2}\|x\|_2^2$ on the unit $\ell_4$-ball in $\mathbb{R}^2$, $x = 0$ and $y = (t, t)$,
the Bregman divergence $D_f(y, x) = L t^2$ exceeds $\frac{L 2^{1/4}}{2}\|y\|_4^2 = 2^{-1/4} L t^2$.
The strong $(4 L n^{1/2-1/p}, 0)$-growth property fails as well: at $x = 0$ every point of the ball
is a Frank–Wolfe vertex, and $v = n^{-1/p}(1, \dots, 1)$ gives
$D_f(\eta v, 0) = \frac{L}{2}\eta^2 n^{1-2/p}$, which exceeds $2 L n^{1/2-1/p}\eta^2$ once
$n^{1/2-1/p} > 4$. With $n^{1-2/p}$ in place of $n^{1/2-1/p}$ both claims hold. Example 4.4 inherits
the constant.

**Example 4.4, first part.** For $p \in (1, 2]$, the ball is strongly convex, and Proposition 4.3
with uniform convexity exponent $2$ and the $(\sqrt{2} n^{1/2-1/p}, 1/2)$-Hölderian error bound
gives weak growth with $r = 2\theta/2 = 1/2$, not $r = 1$, and weak $(M, 1)$-growth fails for every
$M$. For the Euclidean unit disk, $f(x) = \frac{1}{2}\|x - y\|_2^2$ with $y = (1, 0)$ and
$x = (1 - s, s/2)$, the Frank–Wolfe vertex is $v = (2/\sqrt{5}, -1/\sqrt{5})$, the Frank–Wolfe gap
is $g(x) \approx 0.118\, s$ and
$D_f(x + \eta(v - x), x) = \frac{\eta^2}{2}\|v - x\|^2 \approx 0.106\, \eta^2$, so the ratio is
unbounded as $s \to 0$. (The second part of the example calls the conclusion of Proposition 4.3
strong growth; it is weak growth.)
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

## Weak growth

```{prf:definition} Weak growth
:label: def-frank-wolfe-affine-invariant-open-loop-weak
:nonumber:

$(C, f)$ has the *weak $(M, r)$-growth property* if
$D_f(x + \eta(v - x), x)\,(f(x) - f(x^\star))^{1-r} \le \frac{M\eta^2}{2}\, g(x)$ for all $x \in C$,
all Frank–Wolfe vertices $v$, all minimizers $x^\star$ and all $\eta \in [0, 1]$.
```

Since $g(x) \ge f(x) - f(x^\star)$, strong $(M, r)$-growth implies weak $(M, r)$-growth. The weaker
property only controls the primal gap, and the rates are capped at $O(t^{-2})$.

```{prf:theorem} Strong $(M, 0)$-growth and weak $(M, r)$-growth
:label: thm-frank-wolfe-affine-invariant-open-loop-weak
:enumerator: 4.1

Let $f$ be convex with a minimizer on $C$, $(C, f)$ with the strong $(M, 0)$- and weak
$(M, r)$-growth properties, $M > 0$, $r \in [0, 1)$, $\ell \ge 1$ and $\varepsilon \in (0, \ell)$.
Every Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$ satisfies, for all $t \ge 1$,

$$
h_t \le e^{\varepsilon\ell} \max\left\{ \eta_{t-1}^{\ell-\varepsilon} \frac{M}{2},\
\eta_{t-1}^{\min\{\ell-\varepsilon, 1/(1-r), 2\}} \left( \left(\frac{\ell
M}{2\varepsilon}\right)^{1/(1-r)} +
\frac{M}{2} \right) \right\}.
$$

Moreover, either $h_t \le (\eta_t \ell M/(2\varepsilon))^{1/(1-r)}$ for infinitely many $t$, or
there is $R \ge 1$ with
$h_t \le h_R (\eta_{t-1}/\eta_{R-1})^{\ell-\varepsilon} e^{\varepsilon\ell/R}$ for all
$t \ge R + 1$.
```

A step whose primal gap is at most $T_i = (\eta_i \ell M/(2\varepsilon))^{1/(1-r)}$ leaves at most
$T_i + \eta_i^2 M/2$, and weak growth turns every other step into a contraction by
$1 - (1 - \varepsilon/\ell)\eta_i$, since then $D_f \le (\varepsilon/\ell)\eta_i g_i$.

```{prf:lemma} The next fast iterate
:label: lem-frank-wolfe-affine-invariant-open-loop-restart
:enumerator: 4.2

Under weak $(M, r)$-growth with $\ell > 1/(1 - r)$ and $\varepsilon \in (0, \ell - 1/(1 - r))$, for
every $R \ge 1$ some $i$ with $R \le i \le \max\{R, U\}$ satisfies
$h_i \le (\eta_i \ell M/(2\varepsilon))^{1/(1-r)}$, where

$$
U = \left\lceil \ell \left( h_R\, \eta_R^{\varepsilon-\ell} \left(\frac{2\varepsilon}{\ell
M}\right)^{1/(1-r)}
e^{\varepsilon\ell/R} \right)^{1/(\ell-\varepsilon-1/(1-r))} - \ell \right\rceil.
$$
```

Otherwise all steps from $R$ to $\max\{R, U\}$ contract, and the choice of $U$ makes the contracted
value fall below the threshold.

## Gaps growth

```{prf:definition} Gaps growth
:label: def-frank-wolfe-affine-invariant-open-loop-gaps
:nonumber:

$(C, f)$ has the *gaps $(m, r)$-growth property* if $m\,(f(x) - f(x^\star))^{1-r} \le g(x)$ for all
$x \in C$, all Frank–Wolfe vertices $v$ and all minimizers $x^\star$.
```

```{prf:definition} Relaxed gaps growth
:label: def-frank-wolfe-affine-invariant-open-loop-relaxed
:nonumber:

A run has the *relaxed gaps growth property* with $(\delta_t)$ from the threshold $S$ on if for
every $t \ge S$ either $h_t < \delta_t$ or $m\, h_t^{1-r} \le g_t$.
```

The relaxed property depends on the run; it is what polytopes provide when the minimizer lies on the
boundary.

```{prf:theorem} Strong $(M, 0)$-growth and relaxed gaps growth
:label: thm-frank-wolfe-affine-invariant-open-loop-relaxed
:enumerator: 5.2

Let $f$ be convex with a minimizer on $C$, $(C, f)$ with the strong $(M, 0)$-growth property,
$M, m > 0$, $r \in (0, 1)$, $\ell \ge 2$, and let the run have the relaxed gaps growth property with
$\delta_t = (\eta_t M/m)^{1/(1-r)}$ from a threshold
$S \ge \max\{1, \lceil 2^{1/r} \ell M/m^{1/r} - \ell \rceil\}$ on. Then for all $t \ge S$,

$$
h_t \le \max\left\{ h_S \left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^\ell,\
\eta_{t-1}^{\min\{\ell, 1/(1-r), 2\}} \left( \left(\frac{M}{m}\right)^{1/(1-r)} + \frac{M}{2}
\right)
\right\}.
$$
```

From $S$ on, $(\eta_i M)^r \le m/2$ and, by Theorem 3.1, $h_i \le \eta_i M$; together with gaps
growth this makes every step with $h_i > \delta_i$ contract the primal gap by $1 - \eta_i$, and
Lemma 3.3 bounds the product.

```{prf:theorem} Strong $(M, 0)$-growth and gaps growth
:label: thm-frank-wolfe-affine-invariant-open-loop-gaps-rate
:enumerator: 5.1

Under the gaps $(m, r)$-growth property, the bound of Theorem 5.2 holds from
$S = \max\{1, \lceil 2^{1/r} \ell M/m^{1/r} - \ell \rceil\}$ on.
```

## Sufficient conditions

Smoothness bounds the Bregman divergence along the Frank–Wolfe segment by
$\frac{L}{2}\eta^2\|v - x\|^2$, so growth properties follow from bounds on $\|v - x\|$ in terms of
the Frank–Wolfe gap. The paper measures distances in the $\mathcal{C}$-norm, the gauge of
$\frac{1}{2}(\mathcal{C} - \mathcal{C})$, which makes all constants affine invariant; the formal
statements hold for every norm.

```{prf:proposition} Smoothness
:label: prop-frank-wolfe-affine-invariant-open-loop-smooth
:enumerator: 2.8

If $\mathcal{C}$ is convex and bounded with diameter $D$ and $f$ is $L$-smooth over $\mathcal{C}$,
then $(\mathcal{C}, f)$ has the strong $(L D^2, 0)$-growth property. In the $\mathcal{C}$-norm,
$D \le 2$ and $M = 4L$.
```

A set $\mathcal{C}$ is *$(\alpha, p)$-uniformly convex* if
$\gamma x + (1 - \gamma) y + \gamma(1 - \gamma)\alpha\|x - y\|^p z \in \mathcal{C}$ for all
$x, y \in \mathcal{C}$, $\gamma \in [0, 1]$ and unit vectors $z$. A Frank–Wolfe vertex then
satisfies $\alpha \|\nabla f(x)\|_* \|x - v\|^p \le g(x)$ (Proposition 2.19 of [Conditional gradient
methods: smoothness, scaling and linear rates](../conditional-gradient-basics/index.md)).

```{prf:proposition} Uniformly convex sets, gradients bounded away from zero
:label: prop-frank-wolfe-affine-invariant-open-loop-uniform-strong
:enumerator: 3.6

If $\mathcal{C}$ is convex and $(\alpha, p)$-uniformly convex, $f$ is $L$-smooth over $\mathcal{C}$
and $\|\nabla f(x)\|_* \ge \lambda > 0$ on $\mathcal{C}$, then $(\mathcal{C}, f)$ has the strong
$(L(\alpha\lambda)^{-2/p}, 2/p)$-growth property.
```

Under a Hölderian error bound the gradient can vanish at the minimizers, but
$(f(x) - f(x^\star))^{1-\theta} \le \mu \|\nabla f(x)\|_*$ (see [Frank–Wolfe: the
core](../frank-wolfe-core/index.md)), which yields weak growth.

```{prf:proposition} Uniformly convex sets and Hölderian error bounds
:label: prop-frank-wolfe-affine-invariant-open-loop-uniform-weak
:enumerator: 4.3

If $\mathcal{C}$ is compact and $(\alpha, p)$-uniformly convex with $p \ge 2$, and $f$ is convex,
$L$-smooth over $\mathcal{C}$ and satisfies a $(\mu, \theta)$-Hölderian error bound with
$\theta \in [0, 1/2]$, then $(\mathcal{C}, f)$ has the weak
$(L(\mu/\alpha)^{2/p}, 2\theta/p)$-growth property.
```

```{prf:proposition} Minimizers in the relative interior
:label: prop-frank-wolfe-affine-invariant-open-loop-interior
:enumerator: 5.3

If $\mathcal{C}$ is compact, $f$ is convex and satisfies a $(\mu, \theta)$-Hölderian error bound
with $\theta \in [0, 1/2]$, and every point of $\operatorname{aff}(\mathcal{C})$ within distance
$\rho > 0$ of a minimizer lies in $\mathcal{C}$, then $(\mathcal{C}, f)$ has the gaps
$(\rho/\mu, \theta)$-growth property.
```

This is the gap bound behind Theorem 3.6 of [Acceleration of Frank–Wolfe algorithms with open-loop
step-sizes](../frank-wolfe-open-loop-acceleration/index.md), and the formal proof reuses it.

## Minimizers in the relative interior of a face

On a polytope, open-loop step sizes accelerate even when the minimizer lies in the relative interior
of a proper face $\mathcal{C}^*$, a setting where line search and short steps do not beat $O(1/t)$
by Wolfe's lower bound. Once the atoms lie in $\mathcal{C}^*$, the iterates approach the face
quickly.

```{prf:lemma} Distance to the active set
:label: lem-frank-wolfe-affine-invariant-open-loop-distance
:enumerator: 5.6

Let $K$ be convex, and let a Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$, $\ell \ge 2$, have its
atoms in $K$ from $t = Q$ on. Then
$\operatorname{dist}(x_t, K) \le (\eta_t/\eta_Q)^2 \operatorname{dist}(x_Q, K)$ for all $t \ge Q$.
```

Each step moves toward a point of $K$ and so contracts the distance by $1 - \eta_t$, and
$(1 - \eta_t)\eta_t^2 \le \eta_{t+1}^2$ for $\ell \ge 2$.

```{prf:proposition} Relaxed gaps growth on the optimal face
:label: prop-frank-wolfe-affine-invariant-open-loop-face
:enumerator: 5.4

Let $\mathcal{C}$ be compact and convex with diameter $D$, and let $f$ be convex and $L$-smooth with
an $L$-Lipschitz gradient, $\|\nabla f\| \le B$ on $\mathcal{C}$ and a $(\mu, \theta)$-Hölderian
error bound with $\theta \in [0, 1/2]$. Let $\mathcal{C}^* \subseteq \mathcal{C}$ be compact and
convex, contain the minimizers, and contain every point of $\operatorname{aff}(\mathcal{C}^*)$
within distance $\rho > 0$ of a minimizer. If a Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$,
$\ell \ge 2$, has its atoms in $\mathcal{C}^*$ from $t = Q$ on, then, with
$m = \rho/(2^{2-\theta}\mu)$ and $M = \max\{(m/\eta_Q)(2DB)^{1-\theta}, (LD + B)D/\eta_Q, LD^2\}$,
the pair $(\mathcal{C}, f)$ has the strong $(M, 0)$-growth property and the run has the relaxed gaps
$(m, \theta)$-growth property with $\delta_t = (\eta_t M/m)^{1/(1-\theta)}$ from $Q$ on.
```

The gap at $x_t$ is compared with the gap of $\mathcal{C}^*$ at a nearest point $\bar{x}_t$ of
$\mathcal{C}^*$, which Proposition 5.3 bounds below by
$(\rho/\mu)(f(\bar{x}_t) - f^\star)^{1-\theta}$. The comparison costs $(LD + B)\|x_t - \bar{x}_t\|$,
and $f(\bar{x}_t) \ge f(x_t) - B\|x_t - \bar{x}_t\|$; by Lemma 5.6 both losses are small once
$f(x_t) - f^\star \ge \delta_t$.

```{prf:corollary} Accelerated rate on the optimal face
:label: cor-frank-wolfe-affine-invariant-open-loop-face
:enumerator: 5.5

Under the hypotheses of Proposition 5.4 with $L, D > 0$ and $\theta \in (0, 1/2]$, let
$S = \max\{1, \lceil 2^{1/\theta}\ell M/m^{1/\theta} - \ell\rceil, Q\}$. For all $t \ge S$,

$$
f(x_t) - f^\star \le \max\left\{(f(x_S) - f^\star)\left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^\ell,
\eta_{t-1}^{\min\{\ell, 1/(1-\theta), 2\}}\left(\left(\frac{M}{m}\right)^{1/(1-\theta)} +
\frac{M}{2}\right)\right\},
$$

which is $O(t^{-1/(1-\theta)})$.
```

On a polytope, strict complementarity makes the atoms lie in the optimal face eventually.

```{prf:lemma} Active-set identification
:label: lem-frank-wolfe-affine-invariant-open-loop-active
:enumerator: 5.7

Let $\mathcal{C} = \operatorname{conv}(\mathcal{V})$ with diameter $D > 0$ and
$F \subseteq \mathcal{V}$, and let $f$ be convex and $L$-smooth with an $L$-Lipschitz gradient,
$L > 0$, with unique minimizer $x^\star$ and a $(\mu, \theta)$-Hölderian error bound,
$\theta \in (0, 1/2]$. If $\langle \nabla f(x^\star), p - x^\star \rangle \ge \kappa > 0$ for
$p \in \mathcal{V} \setminus F$ and $\langle \nabla f(x^\star), p - x^\star \rangle = 0$ for
$p \in F$, every Frank–Wolfe run with $\eta_t = \ell/(t + \ell)$, $\ell \ge 2$, has its atoms in
$\operatorname{conv}(F)$ for $t \ge \lceil \ell L D^2 (2\mu L D/\kappa)^{1/\theta}\rceil$.
```

The baseline rate $f(x_t) - f^\star \le \eta_t L D^2$ (Theorem 3.1 with Proposition 2.8) and the
error bound bring $\nabla f(x_t)$ close to $\nabla f(x^\star)$, and strict complementarity then
separates the vertices of $F$ from the others.

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
- In Theorems 5.1 and 5.2, $r \in (0, 1)$: the threshold involves $1/r$. Theorem 5.1 assumes
  $\ell \ge 2$, as the proof derives it from Theorem 5.2, which uses Theorem 3.1. In Lemma 4.2,
  $\varepsilon < \ell - 1/(1 - r)$ strictly, since the exponent $1/(\ell - \varepsilon - 1/(1-r))$
  must be defined, and the range of $i$ is $R \le i \le \max\{R, U\}$: when $U < R$, the iterate $R$
  itself is below the threshold, while the paper's range $\{R, \dots, U\}$ is empty.
- The sufficient conditions hold for every norm; the paper uses the $\mathcal{C}$-norm. In
  Proposition 3.6 any $p > 0$ is allowed, and in Proposition 5.3 the radius $\rho$ is any radius for
  which the balls of $\operatorname{aff}(\mathcal{C})$ around the minimizers lie in $\mathcal{C}$,
  rather than the distance from the minimizers to the relative boundary.
- In Section 5.2 the statements hold in real normed spaces, with the diameter $D$ in place of the
  bound $2$ on the $\mathcal{C}$-norm diameter; for $D = 2$ the constants are the paper's.
  Proposition 5.4 and Corollary 5.5 hold for every compact convex
  $\mathcal{C}^* \subseteq \mathcal{C}$ that contains the minimizers and has the radius-$\rho$
  property, not only for the optimal face of a polytope, and need no uniqueness of the minimizer.
  $B$ is any bound on the norm of the gradient over $\mathcal{C}$, which is at least the paper's
  constant. Lemma 5.6 keeps $\operatorname{dist}(x_Q, K)$ instead of bounding it by $2$.
:::

## Coverage

This entry covers the measures of optimality, the convergence rates of Sections 3 to 5, the
sufficient conditions of Propositions 2.8, 3.6, 4.3 and 5.3, and the results for minimizers in the
relative interior of a face of a polytope (Proposition 5.4, Corollary 5.5 and Lemmas 5.6 and 5.7).
Not covered are Lemma 2.10 and the examples, which concern $\ell_p$-balls, Hanner's inequality
(Proposition 2.6) and the numerical experiments.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWAffineOpenLoop/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-affine-invariant-open-loop.md
```
