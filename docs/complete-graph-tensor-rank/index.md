---
title: Exact asymptotic rank of complete-graph tensors at every order
---

```{include} ../_generated/provenance/complete-graph-tensor-rank.md
```

Kirill Khoruzhii's [tensor-rank entry](https://lemmata.iol.berlin/abs/2610.00005),
lemmata:2610.00005, proves over every field that the complete-graph tensor
$G_k(d)$ satisfies

$$
d^{\lfloor k^2/4\rfloor}\le\widetilde R_F(G_k(d))\le d^{k^2/4},
$$

with equality for even $k$. The exact rectangular matrix multiplication
exponent announced in @openai2026ninefourths supplies the missing quarter
in the exponent when $k$ is odd. This separate entry proves the reduction
and deduces equality for every $k\ge2$. Kirill's original entry and its
formalization are imported unchanged.

The external input is the rectangular lower bound stated below. Lean
proves the explicit coordinate restriction from the complete graph, its
asymptotic-rank monotonicity, the exponent calculation, and the final
implication. The OpenAI lower-bound development is not vendored into this
entry: `RectangularLowerBound F` remains an explicit theorem hypothesis.
The source's
[scope statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/379.md)
and the actual
[`rectangular_exponent` proof](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean)
are pinned here to the release inspected for this deduction.

## Definitions and the rectangular input

Place an EPR tensor $\sum_{a=1}^d e_a\otimes e_a$ on every edge of $K_k$
and group the incident factors at each vertex. The resulting $k$-party
tensor is $G_k(d)$. In coordinates, its coefficient is one precisely when
the labels at the two endpoints of every edge agree, and zero otherwise.
Each vertex space has dimension $d^{k-1}$.

Write
$\widetilde R_F(T)=\inf_{N\ge1} R_F(T^{\boxtimes N})^{1/N}$
for asymptotic rank under Kronecker powers, keeping the parties fixed.
Grouping several parties, and applying linear maps independently at the
resulting parties, cannot increase this quantity.

Let $\langle a,b,c\rangle$ denote the three-party triangle tensor with
edge alphabet sizes $a,b,c$. Up to permuting the parties, it is the
coefficient tensor for multiplying an $a\times b$ matrix by a $b\times c$
matrix. For positive weights sorted as $x\ge y\ge z>0$, the source gives

$$
\omega_F(x,y,z)=x+y+
\frac{\max\{(x+y)z-xy,0\}^2}{4xyz}.
$$ (eq-complete-graph-tensor-rank-rectangle)

Only the following specialization of its lower-bound direction is needed:
for integers $r\ge1$ and $d\ge2$,

$$
d^{\omega_F(r^2,r,r)}
\le\widetilde R_F\bigl(\langle d^{r^2},d^r,d^r\rangle\bigr).
$$ (eq-complete-graph-tensor-rank-input)

This is the standard passage from the arithmetic exponent to asymptotic
tensor rank. A rank decomposition at a fixed base can be iterated under
Kronecker powers; padding intermediate dimensions and using bilinear
evaluation gives the corresponding arithmetic exponent upper bound.
Consequently the external arithmetic exponent lower bound forces the
displayed tensor lower bound. The correspondence includes formal
polynomial identities over finite fields. In Lean this specialization is
stated directly on `rectangle F r d`, the coefficient tensor with the
three independent edge alphabets, rather than on an abstract scalar
standing in for tensor rank.

## The three-block restriction

```{prf:theorem} Rectangular multiplication inside an odd complete graph
:label: thm-complete-graph-tensor-rank-restriction

For every field $F$, $r\ge1$, and $d\ge1$,

$$
\widetilde R_F\bigl(\langle d^{r^2},d^r,d^r\rangle\bigr)
\le\widetilde R_F(G_{2r+1}(d)).
$$
```

```{prf:proof} of [](#thm-complete-graph-tensor-rank-restriction)
:nonumber:

Partition the vertices into $A,B,C$ of sizes $r,r,1$ and group each block
into one party. There are $r^2$ edges between $A$ and $B$, and $r$ edges
from each of them to $C$. Their edge labels form alphabets of sizes
$d^{r^2},d^r,d^r$.

At each grouped party, select the coordinates in which every edge wholly
inside that block has a fixed label, say zero. Both endpoints of an
internal edge are then fixed consistently. This is an independent linear
coordinate projection at each of the three parties. The remaining
coefficient is one exactly when the labels on each of the three
inter-block edge bundles agree at their endpoints. These are precisely
the coefficients of the rectangular triangle tensor.

Applying the same grouping and projections to every Kronecker power
proves the asymptotic-rank inequality. No equality of ranks before and
after grouping is required. The Lean proof constructs these selections,
proves coefficient equality, and applies the imported monotonicity lemmas.
```

## Closing the odd-order gap

```{prf:theorem} Odd complete-graph tensors
:label: thm-complete-graph-tensor-rank-odd

Assume the rectangular lower-bound input
[](#eq-complete-graph-tensor-rank-input). For every field $F$, $r\ge1$,
and $d\ge2$,

$$
\widetilde R_F(G_{2r+1}(d))=d^{r^2+r+1/4}=d^{(2r+1)^2/4}.
$$
```

```{prf:proof} of [](#thm-complete-graph-tensor-rank-odd)
:nonumber:

For $r\ge1$, the weights $r^2,r,r$ are already sorted. The numerator
inside the maximum in [](#eq-complete-graph-tensor-rank-rectangle) is

$$
(r^2+r)r-r^2r=r^2>0.
$$

Hence

$$
\omega_F(r^2,r,r)=r^2+r+\frac{r^4}{4r^4}
=r^2+r+\frac14.
$$

The rectangular lower bound and the three-block restriction give the
lower bound $d^{(2r+1)^2/4}$. The upper bound is exactly
[](#thm-tensor-rank-square-root-graphs), proved in Kirill's entry.
```

```{prf:theorem} Complete-graph equality at every order
:label: thm-complete-graph-tensor-rank-all

Under the same rectangular input, for every field $F$, every $k\ge2$,
and every $d\ge1$,

$$\boxed{\widetilde R_F(G_k(d))=d^{k^2/4}.}$$
```

```{prf:proof} of [](#thm-complete-graph-tensor-rank-all)
:nonumber:

For odd $k$ and $d\ge2$, use the preceding theorem. For even $k$, use
Kirill's equality in [](#thm-tensor-rank-square-root-graphs). When $d=1$,
the original upper and lower bounds both equal one.
```

```{prf:corollary} Exact exponent per edge
:label: cor-complete-graph-tensor-rank-edge

Under the same input, for every $k\ge2$,

$$
\tau_F(K_k)=\frac{k^2/4}{\binom k2}=\frac{k}{2(k-1)}.
$$
```

```{prf:proof} of [](#cor-complete-graph-tensor-rank-edge)
:nonumber:

The imported graph-exponent identity identifies the exponent with
$\log\widetilde R_F(G_k(2))/\log2$. Apply the equality theorem and divide
by the number of edges.
```

| Graph | Earlier flattening exponent | Exact exponent from this reduction |
| --- | --- | --- |
| $K_3$ | $2$ | $9/4$ |
| $K_5$ | $6$ | $25/4$ |
| $K_7$ | $12$ | $49/4$ |
| $K_{2r+1}$ | $r(r+1)$ | $r(r+1)+1/4$ |

This closes the complete-graph gap for odd $k$. The distinct question of
attaining the general cubical bound $n^{k/2}$ for odd-party tensors is not
settled by this argument: for $G_k(d)$, the local dimension is
$n=d^{k-1}$, and its exponent $k^2/4$ is strictly below $k(k-1)/2$ when
$k>2$.

```{literalinclude} ../../lean/Lemmata/CompleteGraphTensorRank/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/complete-graph-tensor-rank.md
```
