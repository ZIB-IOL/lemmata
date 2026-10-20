---
title: LP certificates and formulation reductions
---

```{include} ../_generated/provenance/formulation-reduction.md
```

A formulation lower bound can be obtained by factoring the objective slacks of
an LP and then transporting those factors through a reduction. This entry
formalizes that construction with explicit affine certificates. The lower
bound for the source matrix is an input to the reduction.

Let $I$ index objective functions, let $J$ index feasible combinatorial
solutions, and let $v:I\times J\to\mathbb R$ be their objective values. For
minimization, a bound $\beta_i$ gives the slack matrix

$$
T(i,j)=v(i,j)-\beta_i.
$$

For an $\alpha$-approximation, the intended bound is
$\beta_i=\operatorname{OPT}(i)/\alpha$. The reduction statements below apply to
any specified bounds; proving that a particular expression is the optimum is
a separate application-specific step.

```{prf:definition} An LP with explicit affine certificates
:label: def-formulation-reduction-certificate

A certified LP with $m$ inequalities consists of a real vector space $V$,
affine maps $s_1,\ldots,s_m:V\to\mathbb R$, a realization $z_j\in V$ of each
solution, and affine objectives $\ell_i:V\to\mathbb R$, satisfying

$$
P=\{z\in V:s_l(z)\ge 0\ \text{for all }l\},\qquad
z_j\in P,\qquad \ell_i(z_j)=v(i,j).
$$

It also includes nonnegative numbers $y_{il}$ and $\kappa_i$ such that, for
every $i$ and every $z\in V$,

$$
\ell_i(z)-\beta_i
=\sum_{l=1}^{m}y_{il}s_l(z)+\kappa_i.
$$

The feasible region and the realization map are common to all objectives.
The certificate identity implies $\ell_i(z)\ge\beta_i$ throughout $P$.
```

The Lean structure `CertifiedLP` contains exactly these data. Equations can be
handled by parametrizing the affine hull before choosing $V$. The existence
of the displayed certificates from validity of an affine inequality is the
affine Farkas theorem; **that existence theorem is not formalized in this
entry**. Certificates are supplied explicitly.

```{prf:theorem} Factorization from affine certificates
:label: thm-formulation-reduction-factorization

The slack matrix of a certified LP with $m$ inequalities admits a nonnegative
factorization with $m+1$ factors.
```

```{prf:proof} of [](#thm-formulation-reduction-factorization)
:nonumber:

Evaluate the certificate at $z_j$:

$$
T(i,j)=\sum_{l=1}^{m}y_{il}s_l(z_j)+\kappa_i\cdot 1.
$$

All factors are nonnegative. The $m$ inequalities contribute $m$ factors, and
the row-constant remainder contributes one.
```

```{prf:corollary} Certificates with zero remainder
:label: cor-formulation-reduction-zero-offset

If $\kappa_i=0$ for every row, then $r_+(T)\le m$.
```

```{prf:proof} of [](#cor-formulation-reduction-zero-offset)
:nonumber:

Omit the final row-constant term in the preceding factorization.
```

```{prf:theorem} Transfer to the number of inequalities
:label: thm-formulation-reduction-transfer

Let $S,A,B:I_0\times J_0\to\mathbb R$, and let
$f:I_0\to I$ and $g:J_0\to J$ be maps satisfying

$$
S(i,j)=A(i,j)\,T(f(i),g(j))+B(i,j).
$$

Suppose $A$ and $B$ admit nonnegative factorizations with $a$ and $b$
factors, respectively. If $L\le r_+(S)$, then every certified target LP
with $m$ inequalities satisfies

$$
L\le a(m+1)+b.
$$

Here $L$ is a nonnegative integer. The hypothesis $L\le r_+(S)$ is explicit;
no lower-bound theorem for $S$ is assumed as an axiom.
```

```{prf:proof} of [](#thm-formulation-reduction-transfer)
:nonumber:

The target slack has an $(m+1)$-factor nonnegative factorization. Pull it back
along $f$ and $g$, multiply its factors by those of $A$, and append those of
$B$. The resulting factorization of $S$ has $a(m+1)+b$ factors. Apply the
source lower bound.
```

The maps $f$ and $g$ are independent: the encoded solution $g(j)$ does not
depend on $i$. The multiplier $A(i,j)$ and remainder $B(i,j)$ may depend on
both indices, with their factorization sizes accounted for in the bound.

```{prf:corollary} Transfer with zero remainder in the LP certificates
:label: cor-formulation-reduction-transfer-zero-offset

Under the hypotheses of [](#thm-formulation-reduction-transfer), if every
LP certificate has $\kappa_i=0$, then

$$
L\le am+b.
$$
```

```{prf:proof} of [](#cor-formulation-reduction-transfer-zero-offset)
:nonumber:

Use the $m$-factor certificate construction instead of the $(m+1)$-factor
construction.
```

The next consequences instantiate the transfer for approximation slacks.
They are useful for applying a lower bound for a shifted matching slack matrix
without re-formalizing its rank proof.

```{prf:corollary} Positive costs and a constant shift
:label: cor-formulation-reduction-positive-cost

Let $\alpha>1$, $H>0$, and $\lambda=2(\alpha-1)H$. Let
$q:I\times J\to\mathbb R$, and consider a certified LP with objective values
and bounds

$$
v(i,j)=\lambda q(i,j)+H,\qquad
\beta_i=\frac{\lambda+H}{\alpha}.
$$

If

$$
L\le r_+\!\left(q-\frac{1}{2\alpha}\right),
$$

then its number $m$ of inequalities satisfies $L\le m+1$.
```

```{prf:proof} of [](#cor-formulation-reduction-positive-cost)
:nonumber:

The exact identity

$$
\lambda q(i,j)+H-\frac{\lambda+H}{\alpha}
=\lambda\left(q(i,j)-\frac{1}{2\alpha}\right)
$$

and $\lambda>0$ show that the two matrices have the same nonnegative rank.
The certificate factorization has $m+1$ factors.
```

For a matching application, $H$ is the number of edges in a perfect matching
and $q(i,j)$ counts its crossings of an odd cut. These combinatorial
interpretations and the source exponential rank bound are not hypotheses
silently built into `q`: they must be supplied when applying the corollary.

```{prf:corollary} Bounded additive baseline
:label: cor-formulation-reduction-bounded-baseline

Let $\alpha>1$, let $a_i>0$, and suppose $b_i/a_i\le B$ for all $i$. Set

$$
r_0=\frac{1-(\alpha-1)B}{\alpha}.
$$

Consider a certified LP with

$$
v(i,j)=a_iq(i,j)+b_i,\qquad
\beta_i=\frac{a_i+b_i}{\alpha}.
$$

If $L\le r_+(q-r_0)$, then its number $m$ of inequalities satisfies
$L\le m+2$.
```

```{prf:proof} of [](#cor-formulation-reduction-bounded-baseline)
:nonumber:

Divide each row of the target slack by $a_i$. The identity

$$
q(i,j)-r_0
=\frac{1}{a_i}\left(a_iq(i,j)+b_i-\frac{a_i+b_i}{\alpha}\right)
 +\frac{\alpha-1}{\alpha}\left(B-\frac{b_i}{a_i}\right)
$$

has a nonnegative row-constant final term. It adds at most one factor to the
$(m+1)$-factor certificate construction.
```

The bounded-baseline transfer does not require $r_0>0$. To apply a source
theorem about positive constant shifts, one additionally arranges
$B<1/(\alpha-1)$, which makes $r_0>0$.

```{prf:corollary} Near-exact objective reversal
:label: cor-formulation-reduction-objective-reversal

Let $N>0$, let $v:I\times S\to\mathbb R$ be source values, and let
$c:I\times T\to\mathbb R$ be target costs. Suppose there are maps
$e:S\to T$ and $h:T\to S$, independent of $i$, such that

$$
c(i,e(s))=N-v(i,s),\qquad c(i,e(h(t)))\le c(i,t).
$$

Let $C_i,o_i\in\mathbb R$ satisfy $o_i\ge0$ and $C_i-o_i\ge1/4$.
Consider a certified LP with target costs $c$ and bounds

$$
\beta_i=\frac{N-o_i}{1+1/(4N)}.
$$

If $L\le r_+(C_i-v(i,s))$, then the number $m$ of target inequalities
satisfies $L\le m+2$.
```

```{prf:proof} of [](#cor-formulation-reduction-objective-reversal)
:nonumber:

Evaluate the $(m+1)$-factor target slack factorization at the encoded source
solutions. Add the nonnegative row offset

$$
C_i-o_i-
\left(1-\frac{1}{1+1/(4N)}\right)(N-o_i).
$$

The resulting matrix is $C_i-v(i,s)$ and has at most $m+2$ factors.
The row offset is nonnegative because $C_i-o_i\ge1/4$, $o_i\ge0$,
and $(N-o_i)/(4N+1)\le1/4$.
```

For an edge-cover application, the graph construction supplies the encoding
and completion maps, and $o_i$ is the source maximum. The displayed corollary
does not itself assert that $o_i$ is that maximum; optimum preservation is
proved separately once an upper bound and an attaining solution are supplied.

These results implement the certificate and reduction steps used in
[Affine reductions for LPs and SDPs](https://arxiv.org/abs/1410.8816)
and [Strong reductions for extended formulations](https://arxiv.org/abs/1512.04932).
They do not formalize those papers in their entirety or the source
exponential lower bounds.

```{literalinclude} ../../lean/Lemmata/FormulationReduction/Statement.lean
:language: lean
```

```{literalinclude} ../../lean/Lemmata/FormulationReduction/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/formulation-reduction.md
```
