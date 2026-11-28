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
Pokutta [@iommazzo2025linear], currently the lower bound for the pyramidal width of a product
(Theorem 4.5), its objective for the feasibility problem (Proposition 5.1) and the preparatory
bounds of Lemma A.2; numbers refer to the arXiv version.
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

## The pyramidal width of a product

The paper uses the pyramidal width in the form of Peña and Rodríguez: the smallest distance between
a proper face $F$ of $\mathcal{P} = \operatorname{conv}(\mathcal{V})$ and the convex hull of the
vertices outside $F$. This is the facial distance of [Conditional gradient methods: away-step,
fully-corrective and pairwise Frank–Wolfe](../away-step-frank-wolfe/index.md), where it is shown to
equal the scaling constant that drives the linear rate of away-step Frank–Wolfe (Proposition 2.31
there). The proof for products works with an affine variant.

```{prf:definition} Affine pyramidal width
:label: def-frank-wolfe-product-polytopes-affine-width
:enumerator: 4.2

The affine pyramidal width $\hat{\delta}_{\mathcal{P}}$ of
$\mathcal{P} = \operatorname{conv}(\mathcal{V})$ is the infimum of $\|a - q\|$ over proper faces $F$
of $\mathcal{P}$, points $a$ of the affine hull of $F$ and points $q$ of the convex hull of the
vertices outside $F$.
```

```{prf:corollary} The easy inequality
:label: cor-frank-wolfe-product-polytopes-affine-le
:enumerator: 4.4

The affine pyramidal width is at most the pyramidal width:
$\hat{\delta}_{\mathcal{P}} \le \delta_{\mathcal{P}}$.
```

The paper also proves the reverse inequality, so the two widths coincide (Corollary 4.4, via Lemma
4.3: a closest point in the affine hull of a minimizing face lies in its relative interior).

```{prf:definition} The product polytope
:label: def-frank-wolfe-product-polytopes-product-vertices
:nonumber:

For finite sets $\mathcal{V}_1$ and $\mathcal{V}_2$, the product
$\operatorname{conv}(\mathcal{V}_1) \times \operatorname{conv}(\mathcal{V}_2)$ is the convex hull of
$\mathcal{V}_1 \times \mathcal{V}_2$, taken in the Euclidean product of the two spaces.
```

```{prf:theorem} The pyramidal width of a product, lower bound
:label: thm-frank-wolfe-product-polytopes-product-width
:enumerator: 4.5

Let $\mathcal{V}_1$ and $\mathcal{V}_2$ be finite nonempty sets in real inner product spaces, with
affine pyramidal widths $\hat{\delta}_1$ and $\hat{\delta}_2$. The pyramidal width of
$\operatorname{conv}(\mathcal{V}_1) \times \operatorname{conv}(\mathcal{V}_2)$, in the Euclidean
product, is at least
$\sqrt{\hat{\delta}_1^2 \hat{\delta}_2^2/(\hat{\delta}_1^2 + \hat{\delta}_2^2)}$.
```

A proper face of the product is $F_1 \times F_2$ for faces $F_i$ of the factors, exposed by the two
components of the exposing functional. If both $F_i$ are proper, there are unit vectors $u_i$ with
$\langle u_i, a - q \rangle \ge \gamma_i \ge \hat{\delta}_i$ for $a$ in the affine hull of $F_i$ and
$q$ outside, constant on $F_i$; they are obtained by projecting orthogonally to the direction of the
affine hull. The functional
$\left(\frac{\langle u_1, x \rangle}{\gamma_1} + \frac{\langle u_2, y \rangle}{\gamma_2}\right)/N$
with $N = \sqrt{1/\gamma_1^2 + 1/\gamma_2^2}$ has norm at most $1$ and separates the face from the
remaining vertices with margin $1/N$. If $F_2$ is the whole second factor (or $F_1$ the whole
first), the face is at distance at least $\hat{\delta}_1$ (or $\hat{\delta}_2$), which exceeds the
bound by Lemma A.2.

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

:::{note}
**Differences from the paper.**
- Theorem 4.5 is stated with the affine pyramidal widths of the factors in the lower bound. With
  Corollary 4.4 (the two widths coincide, not yet formalized), this is the paper's lower bound; the
  matching upper bound is not formalized yet. The proof also treats the faces
  $F_1 \times \mathcal{P}_2$ and $\mathcal{P}_1 \times F_2$ of the product, which the paper's
  argument, written for two proper factor faces, does not mention.
- The objective of Proposition 5.1 is defined on the Euclidean product of copies of any real inner
  product space, and the proof uses the orthogonal projection onto the complement of the diagonal
  instead of the Hessian.
:::

## Coverage

This entry currently covers the lower bound of Theorem 4.5 with the easy half of Corollary 4.4,
Proposition 5.1 and Lemma A.2. Lemma 4.3 and the other half of Corollary 4.4, the upper bound of
Theorem 4.5, the vertex-facet distance (Proposition 4.7), the products of $k$ polytopes (Corollary
A.3) and the linear rates (Propositions 4.8 and 4.9) are planned; the experiments are not covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWProduct/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-product-polytopes.md
```
