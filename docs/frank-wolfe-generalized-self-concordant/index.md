---
title: "Frank–Wolfe with simple steps for generalized self-concordant functions"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-generalized-self-concordant.md
```

:::{note}
This entry formalizes the paper *Scalable Frank–Wolfe on Generalized Self-concordant Functions via
Simple Steps* by Alejandro Carderera, Mathieu Besançon and Sebastian Pokutta [@carderera2021simple],
currently the monotonic Frank–Wolfe algorithm and its convergence rates (Algorithm 1, Theorems 2.4
and 2.6); numbers refer to the arXiv version.
:::

Many objectives in statistics and machine learning, such as the logistic loss or log-barriers, are
neither globally smooth nor finite everywhere. They are *generalized self-concordant*: a function
$f$ with an open domain is $(M, \nu)$-generalized self-concordant if its third derivative is bounded
by its Hessian,

$$
|\langle D^3 f(x)[w] u, u \rangle| \le M \|u\|_{\nabla^2 f(x)}^2 \|w\|_{\nabla^2 f(x)}^{\nu - 2}
\|w\|_2^{3 - \nu}.
$$

The standard analyses of the Frank–Wolfe algorithm need a smoothness constant, and a step of the
Frank–Wolfe algorithm with the simple step size $\gamma_t = 2/(t + 2)$ can leave the domain. The
paper shows that a tiny modification suffices: reject a step whenever it leaves the domain or
increases the objective.

## Monotonic Frank–Wolfe

```{prf:definition} Monotonic Frank–Wolfe
:label: def-frank-wolfe-generalized-self-concordant-run
:nonumber:

A run of monotonic Frank–Wolfe on $\mathcal{X}$ for $f$ with domain $\operatorname{dom} f$ starts at
$x_0 \in \mathcal{X} \cap \operatorname{dom} f$, picks a Frank–Wolfe vertex $v_t$ for
$\nabla f(x_t)$, and sets $x_{t+1} = x_t + \gamma_t (v_t - x_t)$ with $\gamma_t = 2/(t + 2)$ if this
point lies in $\operatorname{dom} f$ and does not increase $f$; otherwise $x_{t+1} = x_t$.
```

Generalized self-concordance controls the objective near every point of its domain: by results of
Sun and Tran-Dinh (Proposition 2.1 and Lemma 2.3 of the paper), a step that is short in the local
norm stays in the domain and satisfies a quadratic upper bound with the factor $\omega_\nu(1/2)$
(Remark 2.2). Since the iterates of monotonic Frank–Wolfe stay in the sublevel set $\mathcal{L}_0$
of $x_0$, on which the Hessian is bounded by $L$, this yields the following property from the
iteration $T_\nu$ on, with $K = L D^2 \omega_\nu(1/2)$; the formal statements assume it.

```{prf:definition} Local descent
:label: def-frank-wolfe-generalized-self-concordant-descent
:nonumber:

$f$ has the local descent property with step bound $\bar{\gamma}$ and constant $K$ if for every
$y \in \mathcal{X} \cap \operatorname{dom} f$ with $f(y) \le f(x_0)$, every $w \in \mathcal{X}$ and
every $\gamma \in [0, \bar{\gamma}]$, the point $y + \gamma (w - y)$ lies in $\operatorname{dom} f$
and $f(y + \gamma (w - y)) \le f(y) + \gamma \langle \nabla f(y), w - y \rangle + \gamma^2 K$.
```

```{prf:theorem} Primal gap of monotonic Frank–Wolfe
:label: thm-frank-wolfe-generalized-self-concordant-rate
:enumerator: 2.4

Let $f$ be convex on $\mathcal{X} \cap \operatorname{dom} f$ with a minimizer $x^\star$ there, and
let it have the local descent property with step bound $2/(T + 2)$ and constant $K \ge 0$. Every run
of monotonic Frank–Wolfe satisfies, for all $t \ge T$,

$$
f(x_t) - f(x^\star) \le \frac{4 (T + 1)}{t + 1} \max\{f(x_0) - f(x^\star), K\}.
$$
```

The iterates stay in the sublevel set, and from $T$ on the candidate point obeys the quadratic
bound. If $\gamma_t h_t > \gamma_t^2 K$ for the primal gap $h_t$, the candidate decreases $f$ and is
accepted, and $h_{t+1} \le (1 - \gamma_t) h_t + \gamma_t^2 K$; otherwise $h_t \le \gamma_t K$
already, and monotonicity carries the bound to $t + 1$.

```{prf:theorem} Frank–Wolfe gap of monotonic Frank–Wolfe
:label: thm-frank-wolfe-generalized-self-concordant-gap
:enumerator: 2.6

Under the assumptions of Theorem 2.4 with $T \ge 1$, for every $N \ge T + 6$ some iteration
$1 \le t \le N$ has Frank–Wolfe gap

$$
g_t \le \frac{18 N}{N - T} \left( \frac{T + 1}{2T + N - 3} + \frac{2N - 2T + 3}{(2T + N)^2} \right)
\max\{f(x_0) - f(x^\star), K\} = O(1/N).
$$
```

Consider the iterations between $T + \lceil (N - T)/3 \rceil - 2$ and $N - 2$. Either one of them
has $g_t \le \gamma_t K$, or every step there is accepted with progress at least
$\gamma_t g_t - \gamma_t^2 K$; if all gaps exceeded the bound, the accumulated progress would make
the primal gap negative.

:::{note}
**Differences from the paper.**
- Generalized self-concordance enters through the local descent property, which the paper derives
  from Proposition 2.1, Remark 2.2 and Lemma 2.3 (results of Sun and Tran-Dinh) with
  $K = L D^2 \omega_\nu(1/2)$ and step bound $2/(T_\nu + 2)$. The theorems hold for every function
  with this property, in real normed spaces, with the domain any convex set.
- $T$ is a natural number; the paper's $T_\nu$ can be $-1$, in which case $T = 0$ serves.
- Theorem 2.6 assumes $T \ge 1$. For $T_\nu \le 0$ the paper's proof can pick the iteration $0$,
  which the minimum over $1 \le t \le N$ excludes, and $2T_\nu + N - 3$ can vanish; since the local
  descent property for a step bound also holds for every smaller bound, $T$ can always be taken at
  least $1$.
:::

## Coverage

This entry currently covers Algorithm 1 and Theorems 2.4 and 2.6. The results of Sun and Tran-Dinh
behind the local descent property (Proposition 2.1, Lemma 2.3) and Remark 2.2 are cited, not
formalized. The improved rates (Theorems 2.11, 2.15 and 2.16), the away-step and blended pairwise
variants (Section 3), the stateless step size variant and the experiments are not covered yet.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWSelfConcordant/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-generalized-self-concordant.md
```
