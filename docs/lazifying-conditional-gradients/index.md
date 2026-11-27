---
title: "Lazifying conditional gradient algorithms: LCG, LPCG and parameter-free LCG"
numbering:
  headings: false
---

```{include} ../_generated/provenance/lazifying-conditional-gradients.md
```

:::{note}
This entry formalizes the paper *Lazifying Conditional Gradient Algorithms* by Gábor Braun,
Sebastian Pokutta and Daniel Zink [@braun2016lazifying], without its lazy local and online variants
(Sections 3.3 and 5); numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Algorithm 2.** Line 4 calls the linear optimization oracle as
$y \leftarrow \operatorname{argmax}_{x \in P} cx$. For the negative answer to certify
$c(x - z) \le \Phi$ for all $z \in P$, the oracle has to minimize $cx$; the formal statement uses a
minimizer.
:::

The Frank–Wolfe algorithm calls a linear optimization oracle in every iteration. Lazification
replaces it by a weak separation oracle: it only has to find a point that improves the linear
objective by a fixed fraction $\Phi/K$ of a target value $\Phi$, or certify that no point improves
it by more than $\Phi$. Improving points can often be found among vertices computed earlier, and a
full linear optimization is needed only for the certificate. The objects are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md); $P$ is a convex set in a real normed space.

## Weak separation

```{prf:definition} Weak separation oracle (Oracle 1)
:label: def-lazifying-conditional-gradients-weak-sep
:nonumber:

Given a linear objective $c$, a point $x \in P$, a target $\Phi > 0$ and an accuracy $K \ge 1$, the
weak separation oracle either returns a vertex $y$ with $c(x - y) > \Phi/K$ (a positive answer), or
answers *false*, certifying $c(x - z) \le \Phi$ for all $z \in P$ (a negative answer).
```

```{prf:definition} Weak separation via linear optimization (Algorithm 2)
:label: def-lazifying-conditional-gradients-lp-sep
:nonumber:

If a cached vertex $y$ has $c(x - y) > \Phi/K$, return it. Otherwise call the linear optimization
oracle for a minimizer $y_0$ of $c$ over the vertices, and return $y_0$ if $c(x - y_0) > \Phi/K$
and *false* if not.
```

```{prf:proposition} Algorithm 2 answers correctly
:label: prop-lazifying-conditional-gradients-lp-sep
:nonumber:

If the cache consists of vertices, $K \ge 1$ and $\Phi \ge 0$, every answer of Algorithm 2 is a
valid answer of the weak separation oracle for $P = \operatorname{conv} V$.
```

A negative answer comes with $c(x - y_0) \le \Phi/K \le \Phi$ for the minimizer $y_0$, and
$c y_0 \le c z$ for every $z \in P$.

## Lazy conditional gradients

```{prf:definition} Curvature
:label: def-lazifying-conditional-gradients-curvature
:nonumber:

A differentiable function $f$ has curvature at most $C$ on $P$ if
$f(x + \gamma(v - x)) \le f(x) + \gamma f'(x)(v - x) + C\gamma^2/2$ for all $x, v \in P$ and
$\gamma \in [0, 1]$.
```

For an $L$-smooth function, $C = LD^2$ works, where $D$ is the diameter of $P$.

```{prf:definition} Lazy conditional gradient run (Algorithm 3)
:label: def-lazifying-conditional-gradients-lcg
:nonumber:

Starting from $x_1 \in P$, iteration $t \ge 1$ sets
$\Phi_t = (\Phi_{t-1} + C\gamma_t^2/2)/(1 + \gamma_t/K)$ and asks the weak separation oracle about
$f'(x_t)$, $x_t$ and $\Phi_t$. After a positive answer $v_t$, $x_{t+1} = (1 - \gamma_t)x_t +
\gamma_t v_t$; after a negative answer, $x_{t+1} = x_t$.
```

```{prf:theorem} Lazy conditional gradients
:label: thm-lazifying-conditional-gradients-lcg
:enumerator: 3.1

Let $P$ be convex and $f$ convex and differentiable with curvature $C$ on $P$, let $K \ge 1$,
$\gamma_t = 2(K^2 + 1)/(K(t + K^2 + 2))$ and $f(x_1) - f(x^*) \le \Phi_0$. Every run of Algorithm 3
satisfies $f(x_t) - f(x^*) \le 2\max\{C, \Phi_0\}(K^2 + 1)/(t + K^2 + 2)$ for $t \ge 1$.
```

By induction, $f(x_t) - f(x^*) \le \Phi_{t-1}$: a positive answer gains $\gamma_t\Phi_t/K$, which is
exactly what the definition of $\Phi_t$ accounts for, and a negative answer certifies
$f(x_t) - f(x^*) \le f'(x_t)(x_t - x^*) \le \Phi_t$. With this step size,
$\Phi_{t-1} \le 2\max\{C, \Phi_0\}(K^2 + 1)/(t + K^2 + 2)$.

## Parameter-free lazy conditional gradients

The algorithm of Theorem 3.1 cannot do better than its worst-case schedule for $\Phi_t$. The
parameter-free variant keeps $\Phi$ fixed after positive answers, uses line search, and halves
$\Phi$ after every negative answer.

```{prf:definition} Parameter-free lazy conditional gradient run (Algorithm 7)
:label: def-lazifying-conditional-gradients-param-free
:nonumber:

Starting from $x_1 \in P$, iteration $t \ge 1$ asks the weak separation oracle about $f'(x_t)$,
$x_t$ and $\Phi_{t-1}$. After a positive answer $v_t$, $x_{t+1}$ minimizes $f$ on the segment
$[x_t, v_t]$ and $\Phi_t = \Phi_{t-1}$; after a negative answer, $x_{t+1} = x_t$ and
$\Phi_t = \Phi_{t-1}/2$.
```

```{prf:theorem} Parameter-free lazy conditional gradients
:label: thm-lazifying-conditional-gradients-param-free
:enumerator: 4.2

Let $P$ be convex and $f$ convex and differentiable with curvature $C > 0$ on $P$, let $K \ge 1$
and $f(x_1) - f(x^*) \le 2\Phi_0$. For $\varepsilon > 0$, every run of Algorithm 7 satisfies
$f(x_{N+1}) - f(x^*) \le \varepsilon$ once
$N \ge \lceil \log_2(\Phi_0/\varepsilon) \rceil + 1 + 4K\lceil \log_2(\Phi_0/(KC)) \rceil_+ +
16K^2C/\varepsilon$.
```

```{prf:corollary} Few negative answers
:label: cor-lazifying-conditional-gradients-negatives
:enumerator: 4.3

As long as $f(x_{N+1}) - f(x^*) > \varepsilon$, at most
$\lceil \log_2(\Phi_0/\varepsilon) \rceil$ of the iterations $1, \dots, N$ received a negative
answer; so at most $\lceil \log_2(\Phi_0/\varepsilon) \rceil + 1$ negative answers occur before
the primal gap is at most $\varepsilon$.
```

Negative answers keep $f(x_{t+1}) - f(x^*) \le 2\Phi_t$, and $\Phi$ is halved once per negative
answer. A positive answer gains at least $q(\Phi) = \min\{\Phi/(2K), \Phi^2/(2CK^2)\}$, so while
$\Phi$ stays fixed there are at most $2\Phi/q(\Phi)$ positive answers. That is $4K$ for
$\Phi > KC$, and $4CK^2/\Phi$ for $\Phi \le KC$; summed over the halvings with
$\Phi > \varepsilon/2$, the latter form a geometric series below $16K^2C/\varepsilon$.

:::{note}
**Differences from the paper.** Iterates are indexed from $x_1$ as in the paper. Theorem 4.2 is
stated for every $\Phi_0$ with $f(x_1) - f(x^*) \le 2\Phi_0$, as Remark 4.1 allows, and its
logarithmic term $\lceil \log_2(\Phi_0/(KC)) \rceil$ is read as $0$ when
$\Phi_0 < KC$.
:::

## Not yet covered

Lazy pairwise conditional gradients (Theorem 3.2) and weak separation through augmentation
(Proposition 6.1) are not yet covered. The lazy local variant (Section 3.3) and the online variant
(Section 5) are out of scope.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/LazyCG/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/lazifying-conditional-gradients.md
```
