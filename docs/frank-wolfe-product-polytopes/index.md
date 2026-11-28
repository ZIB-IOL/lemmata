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
Pokutta [@iommazzo2025linear], currently the bounds on the pyramidal width of a product (Theorem
4.5), the linear rate of away-step Frank–Wolfe over a product of two polytopes (Proposition 4.8),
its objective for the feasibility problem (Proposition 5.1) and the preparatory bounds of Lemma A.2;
numbers refer to the arXiv version.
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

For the matching upper bound, the paper's pyramidal width (the facial distance) of each factor is
attained by a proper face $F_i$ and points $p_i \in F_i$, $q_i$ in the hull of the remaining
vertices, at distance $\delta_i$; this needs at least two vertices, as in the paper's definition.
The point $p = (p_1, p_2)$ lies in the face $F_1 \times F_2$, the point
$q = \theta (p_1, q_2) + (1 - \theta)(q_1, p_2)$ with
$\theta = \delta_1^2/(\delta_1^2 + \delta_2^2)$ lies in the hull of the remaining vertices, and

$$
\|p - q\|^2 = (1 - \theta)^2 \delta_1^2 + \theta^2 \delta_2^2 =
\frac{\delta_1^2\delta_2^2}{\delta_1^2 + \delta_2^2}.
$$

```{prf:theorem} The pyramidal width of a product, upper bound
:label: thm-frank-wolfe-product-polytopes-product-width-upper
:enumerator: 4.5

If $\mathcal{V}_1$ and $\mathcal{V}_2$ have at least two points each, with pyramidal widths
$\delta_1$ and $\delta_2$, then the pyramidal width of
$\operatorname{conv}(\mathcal{V}_1) \times \operatorname{conv}(\mathcal{V}_2)$ is at most
$\sqrt{\delta_1^2 \delta_2^2/(\delta_1^2 + \delta_2^2)}$.
```

## Linear convergence

The pyramidal width bounds the progress of away-step Frank–Wolfe. The away-step entry shows that the
facial distance is a scaling constant, so the lower bound of Theorem 4.5 is one for the product, and
the linear rate under sharpness of [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and
BCG](../conditional-gradient-improvements/index.md) (Corollary 3.33 with $\theta = 1/2$) applies.
Sharpness with exponent $1/2$ is quadratic growth.

```{prf:proposition} Linear rates via the pyramidal width of the product
:label: prop-frank-wolfe-product-polytopes-rate
:enumerator: 4.8

Let $\mathcal{V}_1$ and $\mathcal{V}_2$ be finite sets in finite-dimensional real inner product
spaces with positive affine pyramidal widths,
$\alpha^2 = \hat{\delta}_1^2\hat{\delta}_2^2/(\hat{\delta}_1^2 + \hat{\delta}_2^2)$, and let $f$ be
convex and $L$-smooth with $\mu$-quadratic growth on
$\mathcal{P} = \operatorname{conv}(\mathcal{V}_1) \times \operatorname{conv}(\mathcal{V}_2)$:
$\frac{\mu}{2}\operatorname{dist}(y, \Omega^\star)^2 \le f(y) - f^\star$. Every run of away-step
Frank–Wolfe over $\mathcal{P}$ satisfies, with $D$ the diameter of
$\mathcal{V}_1 \times \mathcal{V}_2$,

$$
f(x_t) - f^\star \le \left(1 - \min\left\{\frac{1}{2}, \frac{\mu \alpha^2}{16 L
D^2}\right\}\right)^{\lfloor (t-1)/2 \rfloor}
\frac{L D^2}{2}.
$$
```

By Lemma A.2, $\alpha \ge \min\{\hat{\delta}_1, \hat{\delta}_2\}/\sqrt{2}$.

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
- Theorem 4.5 is stated as two bounds: below by the affine pyramidal widths of the factors, above by
  their pyramidal widths (for factors with at least two vertices, as in the paper's definition).
  With Corollary 4.4 (the two widths coincide, not yet formalized), the bounds agree and give the
  paper's equality. The proof of the lower bound also treats the faces $F_1 \times \mathcal{P}_2$
  and $\mathcal{P}_1 \times F_2$ of the product, which the paper's argument, written for two proper
  factor faces, does not mention.
- The objective of Proposition 5.1 is defined on the Euclidean product of copies of any real inner
  product space, and the proof uses the orthogonal projection onto the complement of the diagonal
  instead of the Hessian.
- Proposition 4.8 is stated for two factors and assumes quadratic growth on the product polytope.
  The paper assumes the PL inequality and uses its equivalence with quadratic growth for convex
  functions, which is a statement about unconstrained minimization; the proof uses quadratic growth.
  For two factors the rate constant $\alpha \ge \min\{\hat{\delta}_1, \hat{\delta}_2\}/\sqrt{2}$ is
  better than the paper's $\min\{\delta_1, \delta_2\}/2$ for $k = 2$.
:::

## Coverage

This entry currently covers both bounds of Theorem 4.5 with the easy half of Corollary 4.4,
Proposition 4.8 for two factors, Proposition 5.1 and Lemma A.2. Lemma 4.3 and the other half of
Corollary 4.4, the vertex-facet distance (Propositions 4.7 and 4.9) and the products of $k$
polytopes (Corollary A.3) are planned; the experiments are not covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWProduct/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-product-polytopes.md
```
