---
title: "Linear convergence of Frank–Wolfe over product polytopes"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-product-polytopes.md
```

:::{note}
This entry formalizes the paper *Linear Convergence of the Frank–Wolfe Algorithm over Product
Polytopes* by Gabriele Iommazzo, David Martínez-Rubio, Francisco Criado, Elias Wirth and Sebastian
Pokutta [@iommazzo2025linear], currently its objective for the feasibility problem (Proposition 5.1)
and the preparatory bounds of Lemma A.2; numbers refer to the arXiv version.
:::

Away-step and pairwise Frank–Wolfe converge linearly over polytopes, at a rate governed by a
condition number of the polytope such as its pyramidal width (see [Conditional gradient methods:
away-step, fully-corrective and pairwise Frank–Wolfe](../away-step-frank-wolfe/index.md)). Many
problems are posed over products of polytopes $\mathcal{P}_1 \times \cdots \times \mathcal{P}_k$,
and the paper shows that the product is well conditioned when its factors are. For two factors the
pyramidal width of the product is $\delta_1 \delta_2/\sqrt{\delta_1^2 + \delta_2^2}$, which lies
between $\min\{\delta_1, \delta_2\}/\sqrt{2}$ and $\min\{\delta_1, \delta_2\}$ (Lemma A.2). As an
application, a point in the intersection of $k$ polytopes can be approximated by running Frank–Wolfe
over their product on an objective that penalizes the distances between the blocks.

## The feasibility objective

```{prf:definition} The feasibility objective
:label: def-frank-wolfe-product-polytopes-objective
:nonumber:

On the Euclidean product of $k$ copies of a real inner product space, the objective is
$f(x) = \frac{1}{2k} \sum_{i < j} \|x^i - x^j\|^2$ for $x = (x^1, \dots, x^k)$.
```

```{prf:proposition} Convexity, smoothness and PL
:label: prop-frank-wolfe-product-polytopes-objective
:enumerator: 5.1

The objective $f$ is differentiable and convex, $1$-smooth with a $1$-Lipschitz gradient, and
$\|\nabla f(x)\|^2 = 2 f(x)$. Since $f \ge 0$, it is $1$-PL:
$\frac{1}{2}\|\nabla f(x)\|^2 \ge f(x) - f^\star$.
```

With the mean $\bar{x} = \frac{1}{k}\sum_j x^j$, the identity
$\sum_{i < j} \|x^i - x^j\|^2 = k \sum_i \|x^i - \bar{x}\|^2$ writes $f(x) = \frac{1}{2}\|c(x)\|^2$
for the centering map $c(x) = (x^i - \bar{x})_i$. This map is the orthogonal projection onto the
complement of the diagonal, so $\nabla f(x) = c(x)$ and $\|c(h)\| \le \|h\|$. If the polytopes
intersect, $f^\star = 0$, and a point with $f(x) \le \varepsilon^2/(2k)$ has all its blocks within
distance $\varepsilon$ of each other.

## Preparatory bounds

```{prf:lemma} Preparatory bounds
:label: lem-frank-wolfe-product-polytopes-preparatory
:enumerator: A.2

For $a, b > 0$,
$\frac{1}{\sqrt{2}}\min\{a, b\} \le \sqrt{\frac{a^2 b^2}{a^2 + b^2}} < \min\{a, b\}$, and the middle
term is nondecreasing in $a$ and in $b$.
```

## Coverage

This entry currently covers Proposition 5.1 and Lemma A.2. The conditioning results of Section 4
(the pyramidal width and the vertex-facet distance of products, Theorem 4.5 and Proposition 4.7) and
the linear rates (Propositions 4.8 and 4.9) are planned; the experiments are not covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWProduct/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-product-polytopes.md
```
