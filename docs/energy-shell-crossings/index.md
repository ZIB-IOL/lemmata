---
title: Exact-energy crossing decompositions and balanced fusion
---

```{include} ../_generated/provenance/energy-shell-crossings.md
```

The integral fermionic crossing construction of @khoruzhii2026crossing gives a
decomposition of an identity tensor across two cuts. This entry refines that
construction by choosing both alphabets on exact energy levels, then composes
the resulting crossings along a balanced binary tree. The original identity,
dual families and Fock-space definitions are imported from Khoruzhii's existing
formalization; the refinements below have their own entry and Lean namespace.

For a finite occupation state $I\subset\mathbb N$, put

$$
\mathrm e(I)=\sum_{i\in I}\left(i+\tfrac12\right),\qquad
p(t)=\#\{I:\mathrm e(I)=t\},\qquad
Q(T)=\#\{I:\mathrm e(I)\le T\}.
$$

The finite crossing, sum-of-squares and fusion statements are the formal results
of this entry. The later asymptotic estimates additionally use a classical
partition theorem and are presented separately from the Lean formalization.

## Exact energy levels

For integer $t$, the exact-level count $p(t)$ is `partitionDimension (2 * t)`. The cumulative count
$Q(T)$ includes both integer and half-integer energies. Restricting the action
space to one exact energy level removes the mode coordinate from the rank index.
The capacity assumptions below differ from those of
[](#lem-crossing-decomposition-integral): both alphabets now lie in exact levels.

::::{prf:theorem} Crossing on two energy levels
:label: thm-energy-shell-crossings-integral

Let $H,E,n,m$ be nonnegative integers with $H>0$, $n\le p(H)$ and $m\le p(E)$.
There are integer matrices $A_s,B_s,C_s,D_s\in\mathbb Z^{n\times m}$,
$1\le s\le Q(H+E)$, such that

$$
\delta_{ik}\delta_{j\ell}
=\sum_s (A_s)_{ij}(B_s)_{k\ell}
 +\sum_s (C_s)_{i\ell}(D_s)_{kj}.
$$

Thus each of the two cuts has at most $Q(H+E)$ rank coordinates.
::::

::::{prf:proof} of [](#thm-energy-shell-crossings-integral)
:nonumber:

Choose wire labels of energy $H$ and action labels of energy $E$. In the first
cut, a mode $r$ can contribute through an intermediate state $s$ only when
$\mathrm e(s)-E=r$. The corresponding factor on the other side has the same
condition. Consequently, for $r\ne t$ the mixed product $A_{r,s}B_{t,s}$ vanishes,
entry by entry. Therefore

$$
\left(\sum_r A_{r,s}\right)\left(\sum_t B_{t,s}\right)
=\sum_r A_{r,s}B_{r,s},
$$

where the product denotes the outer product of the two coefficient vectors.
For the second cut the condition is $E-\mathrm e(s)=r$, giving the same
orthogonality. Sum the mode coordinate into each of the four factors and absorb
the signed identity's sign into the third factor. Only states of energy at most
$H+E$ remain. The dual family has unit normalization over $\mathbb Z$, so no
division is involved.
::::

::::{prf:corollary} Finite rectangular sum-of-squares bound
:label: cor-energy-shell-crossings-squares

Under the assumptions of [](#thm-energy-shell-crossings-integral), the product
of an $n$-term and an $m$-term sum of squares is a sum of at most $4Q(H+E)$
squares of complex bilinear forms.
::::

::::{prf:proof} of [](#cor-energy-shell-crossings-squares)
:nonumber:

Contract the crossing identity against $x_i x_k y_j y_\ell$. Each cut gives
$Q(H+E)$ products of two bilinear forms. Over $\mathbb C$, replace each product
$uv$ by $((u+v)/2)^2+((u-v)/(2\mathrm i))^2$.
::::

### Consequence of the classical partition asymptotic

The finite statements above use no asymptotic hypothesis. The estimates in this
paragraph additionally use the classical asymptotic for partitions into distinct
odd parts, recorded in @bridges2022asymptotics, Remark 3.3. That analytic input
and the following logarithmic estimates are not part of the Lean formalization.
With $\kappa=\pi/\sqrt3$, it gives

$$
p(h)=\Theta\!\left(h^{-3/4}e^{\kappa\sqrt h}\right),
\qquad
Q(T)=\Theta\!\left(T^{-1/4}e^{\kappa\sqrt T}\right).
$$

The second formula follows by summing the distinct-odd-part coefficients through
doubled energy $2T$; the last $\Theta(\sqrt T)$ coefficients supply the main
contribution. For $n\to\infty$, one can choose an integer $h$ with $p(h)\ge n$ and

$$
\kappa\sqrt h=\log n+\tfrac32\log\log n+O(1).
$$

The finite square bound then gives

$$
\operatorname{SOS}_{\mathbb C}(n,n)
\le 4Q(2h)
=O\!\left(n^{\sqrt2}(\log n)^{(3\sqrt2-1)/2}\right).
$$

This makes the subpolynomial factor explicit; the leading exponent remains
$\sqrt2$. The [finite comparison script](energy_shell_bounds.py) computes the
capacities using integer dynamic programming. For $n=2^{64}$, it chooses
$H=913,E=678$ for the cumulative construction and $h=803$ for the exact-level
construction. Their respective square-count certificates are
$8H Q(H+E)$ and $4Q(2h)$, whose base-two logarithms are approximately $112.806$
and $102.459$. The latter certificate is about $1302$ times smaller. These are
upper bounds from the two constructions, not optimal square counts.

## Balanced fusion of crossings

A transversal cut selects one endpoint from each of $D$ independent identity
wires. Represent a cut by a Boolean mask $c\in\{0,1\}^D$ and write
$z_c(x,y)_j=x_j$ when $c_j=1$, and $z_c(x,y)_j=y_j$ otherwise. A grouped
decomposition is an identity of the form

$$
\prod_{j=1}^D\delta_{x_jy_j}
=\sum_{c\in\mathcal C}\sum_{s=1}^R
 L_{c,s}(z_c(x,y))\,M_{c,s}(z_c(y,x)).
$$

The two factors see complementary endpoint sets. The rank $R$ is per cut;
the total number of products is $|\mathcal C|R$.

::::{prf:theorem} Balanced finite fusion
:label: thm-energy-shell-crossings-balanced

Let $n\ge0$ and let $h_0,h_1,\ldots$ be positive integers. Define
$R_0=n$ and $R_{t+1}=Q(2h_t)$, and assume $R_t\le p(h_t)$ for every $t$.
For each $r\ge0$, the identity on $D=2^r$ wires with labels in $\{1,\ldots,n\}$
has an integral grouped decomposition with rank index size $R_r$ on each of
$2^{D-1}$ distinct transversal cuts. Every cut selects the first wire's
$x$-endpoint.
::::

::::{prf:proof} of [](#thm-energy-shell-crossings-balanced)
:nonumber:

One wire has the usual diagonal factorization with $n$ rank coordinates.
Suppose two child groups each have rank index size $R_t$. Apply
[](#thm-energy-shell-crossings-integral) to these two rank indices, using
$H=E=h_t$. Contract the child rank indices inside the new left and right
factors. The parent retains only the new index of size $Q(2h_t)$.

Each child layout pair produces two parent layouts, according to whether the
right child's orientation is preserved or reversed. The first endpoint of each
child has fixed orientation. It therefore determines the relative-orientation
bit, and the two child masks determine their own layouts. This proves that the
parent masks are distinct. If $C_t$ is the number of layouts, then
$C_0=1$ and $C_{t+1}=2C_t^2$, hence $C_t=2^{2^t-1}$.
::::

Using the classical estimates above, choose $h_t$ to be the least positive
integer with $p(h_t)\ge R_t$. With $L_t=\log R_t$, $n\ge2$, and
$a=(3\sqrt2-1)/2$, the resulting recurrence satisfies

$$
L_{t+1}\le\sqrt2\,L_t+a\log(1+L_t)+O(1).
$$

The constants can be chosen independently of $t$ and $n$. To see that the
accumulated error is uniform in the depth, first use $\log(1+x)=o(x)$ to obtain
$L_t\le C2^t(L_0+1)$ with an absolute $C$. Substitute this coarse bound into
the logarithmic error, divide the recurrence by $(\sqrt2)^{t+1}$, and sum.
Both $\sum_t(\sqrt2)^{-t}$ and $\sum_t t(\sqrt2)^{-t}$ converge. Thus

$$
\log R_r\le\sqrt D\,[\log n+O(\log\log n+1)],\qquad D=2^r.
$$

This estimate concerns the rank of each cut. There are still $2^{D-1}$ cuts.
The finite fusion theorem proves the integral tensor identity and the distinct
cuts; the displayed asymptotic estimate uses the external partition asymptotic.
Turning it into a circuit-size improvement also requires bounds on evaluation
of the contracted factors, coefficient sizes, and the surrounding circuit
construction. Those costs are not bounded by the fusion theorem.

```{literalinclude} ../../lean/Lemmata/EnergyShellCrossings/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/energy-shell-crossings.md
```
