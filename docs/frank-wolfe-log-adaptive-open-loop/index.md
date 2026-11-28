---
title: "Log-adaptive open-loop step-sizes for Frank–Wolfe"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-log-adaptive-open-loop.md
```

:::{note}
This entry formalizes the paper *Adaptive Open-Loop Step-Sizes for Accelerated Convergence Rates of
the Frank–Wolfe Algorithm* by Elias Wirth, Javier Peña and Sebastian Pokutta [@wirth2025adaptive];
numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Lemma 3.1.** The strengthened cumulative-product bound fails for $\varepsilon$ close to $g(S)$.
For the constant $g \equiv 2$, $S = t = 1$ and $\varepsilon = 1.9$, the left side is
$1 - (1 - 0.95) \cdot \frac{2}{3} \approx 0.9667$, while
$(\eta_1/\eta_0)^{g(1) - \varepsilon} = (2/3)^{0.1} \approx 0.9603$. The proof uses
$\sum_{i=S}^{t} \frac{1}{i + k} \ge \log \frac{t + k}{S - 1 + k}$, but the reverse inequality holds.
For $\varepsilon \le g(S) - 1$ the lemma is true: Bernoulli's inequality bounds every factor by
$\left(\frac{i - 1 + g(S)}{i + g(S)}\right)^{g(S) - \varepsilon}$, and the product telescopes. The
proofs of Theorems 3.2 and 4.1 apply the lemma at $\varepsilon$, so the formal theorems assume
$\varepsilon \le g(S) - 1$; the log-adaptive cases use $\varepsilon = 1 \le g(S) - 1$.
:::

The open-loop step sizes $\eta_t = \ell/(t + \ell)$ of [Affine-invariant accelerated rates for
Frank–Wolfe with open-loop step-sizes](../frank-wolfe-affine-invariant-open-loop/index.md) converge
faster for larger $\ell$ under strong growth, at the rate $O(t^{-\ell+\varepsilon} + t^{-1/(1-r)})$,
but $\ell$ has to be fixed in advance and the constants grow with $\ell$. The paper lets $\ell$ grow
with the iteration: $\eta_t = g(t)/(t + g(t))$ for a slowly growing $g$. For the *log-adaptive*
choice $g(t) = 2 + \log(t + 1)$, the best duality gap converges at the rate $\tilde O(t^{-1/(1-r)})$
under strong $(M, r)$-growth, matching every fixed $\ell$ up to logarithmic factors, and the primal
gap at the rate $\tilde O(t^{-1/(1-r)} + t^{-2})$ under weak growth.

The statements hold in real normed spaces, for every Frank–Wolfe run, with any tie-breaking in the
linear minimization oracle; the Bregman divergence, the best duality gap and the growth properties
are those of the affine-invariant entry.

## Adaptive step sizes

```{prf:definition} Adaptive open-loop step sizes
:label: def-frank-wolfe-log-adaptive-open-loop-eta
:nonumber:

For $g \colon \mathbb{N} \to \mathbb{R}$, the step sizes are $\eta_t = \frac{g(t)}{t + g(t)}$.
```

```{prf:definition} Assumptions A1 and A2
:label: def-frank-wolfe-log-adaptive-open-loop-admissible
:nonumber:

$g \colon \mathbb{N} \to \mathbb{R}_{\ge 2}$ is nondecreasing (A1), and
$\frac{t}{g(t)} \le \frac{t + 1}{g(t + 1)}$ for all $t$ (A2).
```

Assumption A2 says that the step sizes are nonincreasing. Both assumptions hold for every constant
$g \equiv \ell \ge 2$, which gives the fixed open-loop step sizes, and for the log-adaptive choice.

```{prf:definition} Log-adaptive step sizes
:label: def-frank-wolfe-log-adaptive-open-loop-log-step
:nonumber:

The log-adaptive choice is $g(t) = 2 + \log(t + 1)$, with
$\eta_t = \frac{2 + \log(t + 1)}{t + 2 + \log(t + 1)}$.
```

```{prf:proposition} The log-adaptive choice is admissible
:label: prop-frank-wolfe-log-adaptive-open-loop-log-admissible
:nonumber:

$g(t) = 2 + \log(t + 1)$ satisfies Assumptions A1 and A2.
```

For A2, $t \log \frac{t + 2}{t + 1} \le \frac{t}{t + 1} \le 2 + \log(t + 1)$.

## The cumulative-product bound

For a fixed $\ell$, the product of the contraction factors $1 - (1 - \varepsilon/\ell)\eta_i$ over a
stretch of iterations is at most $(\eta_t/\eta_{S-1})^{\ell - \varepsilon} e^{\varepsilon\ell/S}$
(Lemma 3.5 of the affine-invariant entry). With adaptive step sizes the exponential factor
disappears.

```{prf:lemma} Strengthened cumulative-product bound
:label: lem-frank-wolfe-log-adaptive-open-loop-product
:enumerator: 3.1

Let $g \colon \mathbb{N} \to \mathbb{R}_{\ge 2}$ be nondecreasing. For integers $1 \le S \le t$ and
$\varepsilon \in (0, g(S) - 1]$,

$$
\prod_{i=S}^{t} \left(1 - \left(1 - \frac{\varepsilon}{g(i)}\right)\eta_i\right) \le
\left(\frac{\eta_t}{\eta_{S-1}}\right)^{g(S) - \varepsilon}.
$$
```

Each factor equals $\frac{i + \varepsilon}{i + g(i)} \le 1 - \frac{\delta}{i + g(S)}$ with
$\delta = g(S) - \varepsilon \ge 1$, which Bernoulli's inequality bounds by
$\left(\frac{i - 1 + g(S)}{i + g(S)}\right)^\delta$. The product telescopes to
$\left(\frac{S - 1 + g(S)}{t + g(S)}\right)^\delta$, and monotonicity of $g$ gives
$\frac{S - 1 + g(S)}{t + g(S)} \le \frac{\eta_t}{\eta_{S-1}}$.

## Strong growth

```{prf:theorem} Strong $(M, r)$-growth
:label: thm-frank-wolfe-log-adaptive-open-loop-strong
:enumerator: 3.2

Let $f$ be convex with a minimizer on $\mathcal{C}$, let $g$ satisfy Assumptions A1 and A2, let
$(\mathcal{C}, f)$ have the strong $(M, r)$-growth property with $M > 0$ and $r \in [0, 1)$, and let
$S \ge 1$ and $\varepsilon \in (0, g(S) - 1]$. Every Frank–Wolfe run with $\eta_t = g(t)/(t + g(t))$
satisfies, for all $t \ge S$, with $k = \min\{g(S) - \varepsilon, 1/(1 - r)\}$,

$$
\mathrm{pd}_t \le \max\left\{ \mathrm{pd}_S \left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^{g(S) -
\varepsilon},\
\left(\frac{M g(t-1)}{2\varepsilon}\right)^{1/(1-r)} \eta_{t-1}^{k} \right\}.
$$
```

A step whose Frank–Wolfe gap is at most $\left(M g(i) \eta_i/(2\varepsilon)\right)^{1/(1-r)}$ leaves
a best duality gap of at most this value; every other step contracts the best duality gap by
$1 - (1 - \varepsilon/g(i))\eta_i$. Lemma 3.1 bounds the contractions since the last small step, and
A2 handles the maximum over its position.

```{prf:theorem} The log-adaptive case
:label: thm-frank-wolfe-log-adaptive-open-loop-log-strong
:enumerator: 3.2

For $g(t) = 2 + \log(t + 1)$, $\varepsilon = 1$ and $S = \lceil e^{1/(1-r)} \rceil$, every run
satisfies, for all $t \ge S$,

$$
\mathrm{pd}_t \le \max\left\{ \frac{\mathrm{pd}_S}{\eta_{S-1}^{1/(1-r)}},\
\left(\frac{M (2 + \log t)}{2}\right)^{1/(1-r)} \right\} \left(\frac{2 + \log t}{t}\right)^{1/(1-r)}
= \tilde O\!\left(t^{-1/(1-r)}\right).
$$
```

The threshold gives $g(S) - 1 \ge 1/(1 - r)$, so $k = 1/(1 - r)$, and
$\eta_{t-1} \le (2 + \log t)/t$.

## Weak growth

```{prf:theorem} Strong $(M, 0)$-growth and weak $(M, r)$-growth
:label: thm-frank-wolfe-log-adaptive-open-loop-weak
:enumerator: 4.1

Let $f$ be convex with a minimizer on $\mathcal{C}$, let $g$ satisfy Assumptions A1 and A2, let
$(\mathcal{C}, f)$ have the strong $(M, 0)$- and weak $(M, r)$-growth properties with $M > 0$ and
$r \in [0, 1)$, and let $S \ge 1$ and $\varepsilon \in (0, g(S) - 1]$. Every Frank–Wolfe run with
$\eta_t = g(t)/(t + g(t))$ satisfies, for all $t \ge S$, with
$k = \min\{g(S) - \varepsilon, 1/(1 - r), 2\}$,

$$
h_t \le \max\left\{ h_S \left(\frac{\eta_{t-1}}{\eta_{S-1}}\right)^{g(S) - \varepsilon},\
\left(\left(\frac{M g(t-1)}{2\varepsilon}\right)^{1/(1-r)} + \frac{M}{2}\right) \eta_{t-1}^{k}
\right\}.
$$
```

```{prf:theorem} The log-adaptive case
:label: thm-frank-wolfe-log-adaptive-open-loop-log-weak
:enumerator: 4.1

For $g(t) = 2 + \log(t + 1)$, $\varepsilon = 1$, $S = \lceil e^{1/(1-r)} \rceil$ and
$b = \min\{1/(1 - r), 2\}$, every run satisfies, for all $t \ge S$,

$$
h_t \le \max\left\{ \frac{h_S}{\eta_{S-1}^{b}},\
\left(\frac{M (2 + \log t)}{2}\right)^{1/(1-r)} + \frac{M}{2} \right\}
\left(\frac{2 + \log t}{t}\right)^{b} = \tilde O\!\left(t^{-1/(1-r)} + t^{-2}\right).
$$
```

Under weak growth the rate is capped at $\tilde O(t^{-2})$ for every choice of $g$, as for the fixed
step sizes.

:::{note}
**Differences from the paper.**
- The statements hold in real normed spaces, for every Frank–Wolfe run, and assume a minimizer.
- Lemma 3.1 and Theorems 3.2 and 4.1 assume $\varepsilon \le g(S) - 1$; see the errata.
- The log-adaptive cases are stated with explicit constants and the factor $(2 + \log t)/t$ in place
  of the $O$-notation. In Theorem 4.1 the paper writes $g(t) = 2 + \log t$, which is undefined at
  $t = 0$; the formalization uses $g(t) = 2 + \log(t + 1)$ as in Theorem 3.2. The paper's statement
  of Theorem 4.1 also writes $g \colon \mathbb{R}_{\ge 0} \to \mathbb{R}_{\ge 0}$; the formalization
  uses $g \colon \mathbb{N} \to \mathbb{R}_{\ge 2}$ as in Assumption A1.
:::

## Coverage

This entry covers the admissibility of the log-adaptive step sizes, Lemma 3.1 (in the corrected
range), Theorems 3.2 and 4.1 and their log-adaptive cases. The numerical experiments are not
covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWLogAdaptive/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-log-adaptive-open-loop.md
```
