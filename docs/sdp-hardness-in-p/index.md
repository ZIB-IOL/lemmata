---
title: SDP hardness of approximation via shifted matching reductions
---

```{include} ../_generated/provenance/sdp-hardness-in-p.md
```

The exponential real PSD-rank bound of @openai2026shifted upgrades three
reductions from [LP hardness in P](https://lemmata.iol.berlin/abs/2610.00004),
lemmata:2610.00004, to unrestricted semidefinite formulations. For every
fixed approximation factor $\alpha>1$, a common SDP supporting all the
specified objectives requires matrix order $2^{\Omega_\alpha(n)}$.

| Problem | Objective family | Shift $\rho$ in the source matrix |
| --- | --- | --- |
| Minimum-cost perfect matching | Strictly positive metric edge costs | $1-1/(2\alpha)$ |
| Minimum-cost $T$-join | $T=V$, with the same metric costs | $1-1/(2\alpha)$ |
| Minimum odd cut | Edge weights in $\{0,1\}$ | $1-1/\alpha$ |

All three problems are polynomial-time solvable. These are bounds on the
size of a single formulation representing every objective in the family;
they impose no symmetry, equivariance, sparsity, or precision condition.

The Lean contribution proves the PSD factorization constructions, the
certificate-to-slack step, and the three finite lower-bound transfers.
It imports the graph domains, edge-sum objectives, and optimum proofs of
the earlier LP entry. The positive-shift PSD-rank theorem is an explicit
hypothesis in every application. OpenAI's
[formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/126.md)
records superpolynomial unshifted exact-matching statements; it does not
formalize the exponential positive-shift theorem used here. The latter is
the external manuscript input, and is not introduced as a Lean axiom.

## Formulation model and source theorem

For a minimization problem with instances $i\in I$, solutions $x\in X$,
and objective values $v(i,x)$, an $\alpha$-approximate SDP consists of an
affine matrix pencil $P(z)\in\mathbb S^m$, feasible realizations $z_x$, and
affine objectives $\ell_i$, satisfying

$$
P(z_x)\succeq0,\qquad \ell_i(z_x)=v(i,x),\qquad
\inf_{P(z)\succeq0}\ell_i(z)\ge\frac{\operatorname{OPT}(i)}{\alpha}.
$$

The parameter space incorporates affine equations. The pencil and
realization map are independent of $i$. For a product of PSD cones, size
means the sum of the block orders, represented by a block diagonal pencil.
Allowing a separate constant-size formulation for each objective would
change the model and would not give the slack matrix considered here.

For even $n$, odd vertex sets $U$, and perfect matchings $M$ of $K_n$, let

$$
q_n(U,M)=|\delta(U)\cap M|,\qquad
A_n(\rho)_{U,M}=q_n(U,M)-1+\rho.
$$

The manuscript theorem of @openai2026shifted gives an absolute $c>0$ such
that for every fixed $0<\rho<1$ and all sufficiently large even $n$,

$$
\operatorname{rank}_{\mathrm{psd},\mathbb R} A_n(\rho)\ge2^{cn}.
$$

Here a size-$m$ factorization means $A(i,x)=\operatorname{tr}(F_iG_x)$
with real PSD $m\times m$ matrices. The entries must be reproduced exactly.
Positive scalar multiplication, transposition, and restriction to selected
rows or columns transfer such factorizations without increasing their size.
The endpoint $\rho=1$ is excluded: $q_n$ itself has an edge-indexed diagonal
factorization of order $\binom n2$.

## From SDP certificates to PSD factors

The formal model `CertifiedSDP` includes PSD matrices $Y_i$ and numbers
$\kappa_i\ge0$ certifying the desired objective bounds $\beta_i$ through

$$
\ell_i(z)-\beta_i=\operatorname{tr}(Y_iP(z))+\kappa_i
\quad\text{for every }z.
$$

For a finite-dimensional formulation with finite objective infima, such
certificates follow from conic duality after restricting to the minimal
face containing the feasible PSD matrices. This face is a PSD cone of
order at most $m$, and its feasible affine section meets its relative
interior. The optimal dual value minus $\beta_i$ is the nonnegative
remainder $\kappa_i$. This certificate-existence step is external to the
Lean development; the certificate identity is part of the formal input.

```{prf:theorem} Certified SDP lower-bound transfer
:label: thm-sdp-hardness-in-p-certificate

Let $S(i,x)=v(i,x)-\beta_i$. A certified SDP of order $m$ gives a real PSD
factorization of $S$ of order $m+1$. Consequently, if every real PSD
factorization of $S$ has order at least $L$, then $L\le m+1$.
```

```{prf:proof} of [](#thm-sdp-hardness-in-p-certificate)
:nonumber:

Evaluate the certificate at each $z_x$. The block diagonal factors
$F_i=\operatorname{diag}(Y_i,\kappa_i)$ and
$G_x=\operatorname{diag}(P(z_x),1)$ are PSD, and their trace product equals
$S(i,x)$. The extra scalar coordinate accounts for the affine remainder.
```

## Matching and joins with positive metric costs

Fix $\alpha>1$, even $n\ge2$, $H=n/2$, and
$\lambda=(\alpha-1)n>0$. For each odd $U\subseteq[n]$, give edge $e$ cost

$$c^U_e=1+\lambda\mathbf1_{\{e\in\delta(U)\}}.$$

These costs are strictly positive off the diagonal and satisfy the triangle
inequality: a triangle crossing the cut has two crossing edges. They are
also tree-metric distances, realized by two star centers joined by an
edge of length $\lambda$, with pendant edges of length $1/2$.

Every perfect matching has $H$ edges and crosses $U$ at least once. Exactly
one crossing can be attained by matching one vertex of $U$ to one of its
complement and matching the remaining vertices within the two sides.
Thus $\operatorname{OPT}(U)=H+\lambda$. The earlier entry proves these
facts on the concrete graph and matching domains.

```{prf:theorem} Minimum-cost perfect matching
:label: thm-sdp-hardness-in-p-matching

If every PSD factorization of $q_n-1/(2\alpha)$ has order at least $L$,
every certified $\alpha$-approximate matching SDP for the displayed costs
has order at least $L-1$. In particular, the shifted-matching theorem gives
order $2^{\Omega_\alpha(n)}$ for every fixed $\alpha>1$.
```

```{prf:proof} of [](#thm-sdp-hardness-in-p-matching)
:nonumber:

The objective value at $M$ is $H+\lambda q_n(U,M)$, and its approximation
slack is

$$
H+\lambda q_n(U,M)-\frac{H+\lambda}{\alpha}
=\lambda\left(q_n(U,M)-\frac1{2\alpha}\right).
$$

Scale the row factors from the certificate theorem by $1/\lambda$.
This produces a factorization of $A_n(1-1/(2\alpha))$ of order $m+1$.
Since $0<1-1/(2\alpha)<1$, the external theorem applies. Subtracting one
from an exponential bound preserves its exponential order.
```

```{prf:theorem} Minimum-cost $T$-join with $T=V$
:label: thm-sdp-hardness-in-p-join

The same finite and exponential SDP lower bounds hold for minimum-cost
$V$-join with the same strictly positive metric costs.
```

```{prf:proof} of [](#thm-sdp-hardness-in-p-join)
:nonumber:

A $V$-join has odd positive degree at every vertex, hence at least $H$
edges, and crosses every odd cut. Its cost is at least $H+\lambda$.
A perfect matching with one crossing attains this value. Retain only the
perfect-matching columns of the $V$-join slack matrix. This inclusion of
solutions is independent of the objective $U$, preserves all costs, and
gives exactly the matching slack matrix above.
```

## Minimum odd cut

For each perfect matching $M$, give edge $e$ weight
$w^M_e=\mathbf1_{\{e\in M\}}$. Every odd cut has value at least one;
a singleton cut attains one.

```{prf:theorem} Minimum odd cut
:label: thm-sdp-hardness-in-p-odd-cut

If every PSD factorization of $q_n-1/\alpha$ has order at least $L$,
every certified $\alpha$-approximate minimum odd-cut SDP for these zero-one
weights has order at least $L-1$. Consequently, its order is
$2^{\Omega_\alpha(n)}$ for each fixed $\alpha>1$.
```

```{prf:proof} of [](#thm-sdp-hardness-in-p-odd-cut)
:nonumber:

The slack with row $M$ and column $U$ is $q_n(U,M)-1/\alpha$, the transpose
of $A_n(1-1/\alpha)$. Swapping the two PSD factor families preserves the
trace product. Apply the certificate theorem and $0<1-1/\alpha<1$.
```

The fourth application in the earlier LP entry, odd-red bipartite matching,
uses a different shifted parity-matching matrix. The ordinary matching PSD
theorem does not supply that matrix's PSD-rank lower bound, so no fourth
SDP consequence is claimed here.

```{literalinclude} ../../lean/Lemmata/SDPHardnessInP/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/sdp-hardness-in-p.md
```
