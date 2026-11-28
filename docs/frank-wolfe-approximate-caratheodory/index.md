---
title: "The approximate Carathéodory problem via Frank–Wolfe"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-approximate-caratheodory.md
```

:::{note}
This entry formalizes the paper *Revisiting the Approximate Carathéodory Problem via the Frank–Wolfe
Algorithm* by Cyrille W. Combettes and Sebastian Pokutta [@combettes2019revisiting], currently its
objective (Lemma 3.1), its cardinality bounds for short steps, for targets in the relative interior
and for projections onto strongly convex sets (Corollaries 5.1, 5.3 and 7.1), and its lower bound
(Theorem 8.1); numbers refer to the arXiv version.
:::

Carathéodory's theorem writes every point $x^\star$ of the convex hull of a set
$\mathcal{V} \subseteq \mathbb{R}^n$ as a convex combination of at most $n + 1$ points of
$\mathcal{V}$. The *approximate Carathéodory problem* asks for far fewer points if $x^\star$ only
has to be approximated: a point $x$ with $\|x - x^\star\|_p \le \varepsilon$ that is a convex
combination of few points of $\mathcal{V}$. The Frank–Wolfe algorithm solves it directly. Minimizing
$f(x) = \frac{1}{2}\|x - x^\star\|_p^2$ over $\operatorname{conv}(\mathcal{V})$ from a vertex, every
iteration adds at most one vertex, so a convergence rate for $f$ turns into a bound on the number of
vertices. The basic bound, $O(p D_p^2/\varepsilon^2)$ vertices for the $\ell_p$-diameter $D_p$ of
$\mathcal{V}$, is formalized in [The Frank–Wolfe algorithm: a short
introduction](../frank-wolfe-introduction/index.md). The paper derives sharper bounds from faster
rates, which need the properties of $f$ in Lemma 3.1, and complements them with a lower bound.

## The objective

```{prf:definition} The objective
:label: def-frank-wolfe-approximate-caratheodory-objective
:nonumber:

For $x^\star \in \mathbb{R}^n$ and $p \in [2, \infty)$, the objective is
$f(x) = \frac{1}{2}\|x - x^\star\|_p^2$.
```

For $p \ge 2$ the derivative of $f$ at $x$ is the functional

$$
h \mapsto \|x - x^\star\|_p^{2-p} \sum_i \operatorname{sign}(x_i - x^\star_i)\,|x_i -
x^\star_i|^{p-1} h_i.
$$

Hölder's inequality bounds its norm by $\|x - x^\star\|_p$, with equality in direction
$x - x^\star$.

```{prf:lemma} The objective
:label: lem-frank-wolfe-approximate-caratheodory-objective
:enumerator: 3.1

Let $p \in [2, \infty)$, $x^\star \in \mathbb{R}^n$ and $f(x) = \frac{1}{2}\|x - x^\star\|_p^2$.
Then $f$ is differentiable and convex, and with respect to the $\ell_p$-norm it is $(p - 1)$-smooth,
with a $(p - 1)$-Lipschitz gradient, and $1$-gradient dominated:
$\|\nabla f(x)\|_{p/(p-1)} = \|x - x^\star\|_p$, so $f(x) = \frac{1}{2}\|\nabla f(x)\|^2_{p/(p-1)}$.
On every set $\mathcal{C}$ containing $x^\star$, $f$ is $\sqrt{2}$-sharp: the distance from $x$ to
the minimizers of $f$ over $\mathcal{C}$ is at most $\sqrt{2}\sqrt{f(x) - \min_{\mathcal{C}} f}$.
```

The smoothness inequality for $\|\cdot\|_p^2$ is proved in the introduction entry. Hölder's
inequality adds the matching lower bound, so the functional above is the Fréchet derivative and the
remainder is at most $(p - 1)\|h\|_p^2$. The Lipschitz constant then follows from the smoothness
inequality and convexity (Lemma 1.7 of [Conditional gradient methods: smoothness, scaling and linear
rates](../conditional-gradient-basics/index.md)).

## Cardinality bounds

The iterate $x_t$ of a run that starts at a vertex is a convex combination of $x_0$ and the atoms
$v_0, \dots, v_{t-1}$.

```{prf:lemma} Sparse iterates
:label: lem-frank-wolfe-approximate-caratheodory-sparsity
:nonumber:

Every Frank–Wolfe run that starts at a point of $\mathcal{V}$ and only uses atoms in $\mathcal{V}$
writes $x_t$ as a convex combination of at most $t + 1$ points of $\mathcal{V}$.
```

Since $\|x_t - x^\star\|_p^2 = 2(f(x_t) - f(x^\star))$, every convergence rate for $f$ bounds the
number of vertices. The corollaries below hold for every short-step run, or more generally every run
whose steps do at least as well as each $s \in [0, 1]$ in the smoothness bound, that starts at a
vertex and uses vertices as atoms; $\mathcal{V}$ is finite with $\ell_p$-diameter $D$.

```{prf:corollary} The general bound
:label: cor-frank-wolfe-approximate-caratheodory-short-step
:enumerator: 5.1

For $x^\star \in \operatorname{conv}(\mathcal{V})$, every such run satisfies
$\|x_t - x^\star\|_p \le \varepsilon$ as soon as $t + 3 \ge 4(p - 1)D^2/\varepsilon^2$, with $x_t$ a
convex combination of at most $t + 1$ vertices.
```

This follows from the rate $2LD^2/(t + 3)$ of Theorem 2.2 of [Conditional gradient methods:
smoothness, scaling and linear rates](../conditional-gradient-basics/index.md) with $L = p - 1$. If
$x^\star$ lies in the relative interior, the iterates converge linearly: the error bound of Lemma
3.1 and an affine ball of radius $r$ around $x^\star$ give $g_t \ge (r/\sqrt{2})\sqrt{h_t}$ (as in
[Acceleration of Frank–Wolfe algorithms with open-loop
step-sizes](../frank-wolfe-open-loop-acceleration/index.md)), and every short step contracts the
primal gap by $1 - 1/K$.

```{prf:corollary} A target in the relative interior
:label: cor-frank-wolfe-approximate-caratheodory-interior
:enumerator: 5.3

If every point of the affine hull of $\operatorname{conv}(\mathcal{V})$ within distance $r > 0$ of
$x^\star$ lies in $\operatorname{conv}(\mathcal{V})$, then with $K = \max\{2, 4(p - 1)D^2/r^2\}$
every such run satisfies $\|x_t - x^\star\|_p \le \varepsilon$ as soon as
$t \ge 1 + K \log((p - 1)D^2/\varepsilon^2)$, with $x_t$ a convex combination of at most $t + 1$
vertices: $O(p (D/r)^2 \log(1/\varepsilon))$ vertices.
```

Over uniformly convex sets the target need not be interior. Since
$\|\nabla f(x)\| = \|x - x^\star\|_p$ and $f \ge 0 = f(x^\star)$, the objective is
$\sqrt{1/2}$-gradient dominated, and Theorem 2.24 of the basics entry gives a rate.

```{prf:corollary} Uniformly convex sets
:label: cor-frank-wolfe-approximate-caratheodory-uniform
:enumerator: 5.5

Let $\mathcal{C}$ be compact, convex and $(\alpha, q)$-uniformly convex with respect to the
$\ell_p$-norm, with $q \ge 2$ and diameter $D$, and let $x^\star \in \mathcal{C}$. With $L = p - 1$,
$K = (L/(2\alpha^2))^{1/(q-1)}$ and $t_0 = \max\{\lfloor \log_2(D^2/K)\rfloor + 1, 1\}$, every
short-step run over $\mathcal{C}$ that starts at a point of $\mathcal{V} \subseteq \mathcal{C}$ and
uses atoms in $\mathcal{V}$ satisfies $\|x_t - x^\star\|_p \le \varepsilon$ as soon as $t \ge t_0$
and $(2LK/\varepsilon^2)^{(q-1)/q} \le 1 + (1 - 1/q)(t - t_0)/2$, with $x_t$ a convex combination of
at most $t + 1$ points of $\mathcal{V}$. This takes $O(\varepsilon^{-2(q-1)/q})$ iterations, and
$O(1/\varepsilon)$ for strongly convex sets ($q = 2$, Corollary 5.4).
```

The same argument gives sparse approximate projections. For $x^\star \notin \mathcal{C}$, the
gradient norm $\|x - x^\star\|_p$ is at least $c = \operatorname{dist}_p(x^\star, \mathcal{C})$ on
$\mathcal{C}$, and over strongly convex sets Theorem 2.20 of the basics entry gives a linear rate.

```{prf:corollary} Sparse approximate projections onto strongly convex sets
:label: cor-frank-wolfe-approximate-caratheodory-projection
:enumerator: 7.1

Let $\mathcal{C}$ be compact, convex and $\alpha$-strongly convex with respect to the $\ell_p$-norm,
with diameter $D$, let $x^\star \notin \mathcal{C}$,
$c = \operatorname{dist}_p(x^\star, \mathcal{C})$ and $K = \max\{2, 2(p - 1)/(\alpha c)\}$. Every
short-step run over $\mathcal{C}$ that starts at a point of $\mathcal{V} \subseteq \mathcal{C}$ (for
instance the extreme points) and uses atoms in $\mathcal{V}$ satisfies
$\|x_t - x^\star\|_p^2 - c^2 \le \varepsilon^2$ as soon as
$t \ge 1 + K \log((p - 1)D^2/\varepsilon^2)$, with $x_t$ a convex combination of at most $t + 1$
points of $\mathcal{V}$.
```

For uniformly convex sets with $q > 2$, Theorem 2.20 of the basics entry gives a sublinear rate
instead.

```{prf:corollary} Sparse approximate projections onto uniformly convex sets
:label: cor-frank-wolfe-approximate-caratheodory-projection-uniform
:enumerator: 7.2

Let $\mathcal{C}$ be compact, convex and $(\alpha, q)$-uniformly convex with respect to the
$\ell_p$-norm, with $q > 2$ and diameter $D$, let $x^\star \notin \mathcal{C}$ and
$c = \operatorname{dist}_p(x^\star, \mathcal{C})$. With $L = p - 1$, $K = (L/(\alpha c))^{2/(q-2)}$
and $t_0 = \max\{\lfloor \log_2(D^2/K)\rfloor + 1, 1\}$, every such run satisfies
$\|x_t - x^\star\|_p^2 - c^2 \le \varepsilon^2$ as soon as $t \ge t_0$ and
$(2LK/\varepsilon^2)^{(q-2)/q} \le 1 + (1/2 - 1/q)(t - t_0)$, with $x_t$ a convex combination of at
most $t + 1$ points of $\mathcal{V}$.
```

## A lower bound

The bound $O(p D_p^2/\varepsilon^2)$ cannot be improved in general. The paper's example uses the
columns of a Hadamard matrix and corrects an earlier lower bound by Mirrokni, Paes Leme, Vladu and
Wong, whose proof uses the inequality $1/(\varepsilon^2 + 1/n) \ge 1/\max\{\varepsilon^2, 1/n\}$;
the inequality holds in the reverse direction.

```{prf:definition} Normalized columns
:label: def-frank-wolfe-approximate-caratheodory-hadamard-vertex
:nonumber:

For a matrix $H$ of order $n$ and $p \in [2, \infty)$, the normalized columns are the points
$H_j/n^{1/p}$ of $\ell_p^n$.
```

```{prf:definition} Barycenter
:label: def-frank-wolfe-approximate-caratheodory-hadamard-center
:nonumber:

The barycenter of the normalized columns is $\frac{1}{n}\sum_j H_j/n^{1/p}$.
```

```{prf:theorem} A lower bound
:label: thm-frank-wolfe-approximate-caratheodory-lower-bound
:enumerator: 8.1

Let $p \in [2, \infty)$, let $H$ be a Hadamard matrix of order $n$ (entries $\pm 1$, orthogonal
columns), let $\mathcal{C}$ be the convex hull of the normalized columns $H_j/n^{1/p}$ and let
$x^\star$ be their barycenter. If $x \in \operatorname{conv}\{H_j/n^{1/p} : j \in S\}$ satisfies
$\|x - x^\star\|_p \le \varepsilon$, then $|S| \ge 1/(\varepsilon^2 + 1/n)$.
```

The paper states the theorem without proof. With $x = \sum_j \lambda_j H_j/n^{1/p}$ and
$\mu_j = \lambda_j - 1/n$, orthogonality of the columns gives
$\|x - x^\star\|_2^2 = n^{1-2/p} \sum_j \mu_j^2$, the power mean inequality gives
$\|y\|_2^2 \le n^{1-2/p}\|y\|_p^2$, and $\sum_j \mu_j^2 = \sum_j \lambda_j^2 - 1/n \ge 1/|S| - 1/n$
by the Cauchy–Schwarz inequality.

:::{note}
**Differences from the paper.**
- Theorem 8.1 is stated for every Hadamard matrix, with the barycenter of the normalized columns.
  The paper uses Sylvester's construction, whose barycenter is $e_1/n^{1/p}$ since its first row is
  all ones and the other rows sum to zero.
- In Lemma 3.1, gradient domination is stated as the identity $\|\nabla f(x)\| = \|x - x^\star\|_p$.
- The cardinality bounds are stated with explicit constants and for every run with steps at least as
  good as the short step, rather than in $O$-notation; the paper's $\ln(1/\varepsilon)$ appears as
  $\log((p - 1)D^2/\varepsilon^2)$. Corollary 5.1 is stated for short steps; the open-loop version
  is the theorem of the introduction entry. Corollaries 5.4, 5.5 and 7.2 have thresholds with the
  constants of the rates in the basics entry; they lead to the paper's orders in $\varepsilon$.
:::

## Coverage

This entry covers Lemma 3.1, Corollaries 5.1 (short steps), 5.3, 5.4, 5.5, 7.1 and 7.2, and Theorem
8.1. Not covered are Corollary 5.2, which uses a version of the nearest extreme point oracle with
diameters in the $\ell_2$-norm and of a sublevel set that the conditional gradient entries do not
formalize, the nonsmooth case $p \in [1, 2) \cup \{\infty\}$ (Section 6) and the experiments; the
rates of Section 4 are cited results, several of which are formalized in other entries.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWCaratheodory/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-approximate-caratheodory.md
```
