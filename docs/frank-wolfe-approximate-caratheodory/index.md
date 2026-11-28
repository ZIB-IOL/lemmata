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
objective (Lemma 3.1) and its lower bound (Theorem 8.1); numbers refer to the arXiv version.
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
:::

## Coverage

This entry currently covers Lemma 3.1 and Theorem 8.1. The cardinality bounds of Section 5, which
apply the rates of Section 4 (several of which are formalized in other entries), the nonsmooth case
$p \in [1, 2) \cup \{\infty\}$ (Section 6), the sparse approximate projections (Section 7) and the
experiments are not covered yet.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWCaratheodory/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-approximate-caratheodory.md
```
