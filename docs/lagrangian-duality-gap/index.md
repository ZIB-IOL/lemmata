---
title: A Lagrangian duality gap that survives closed convexification
authors:
  - name: Geoffrion theorem experiment contributors
---

Replacing an integer feasible set by its closed convex hull need not remove a
Lagrangian duality gap. This example uses four integer variables and two linear
constraints with integral coefficients: all three primal problems attain value
$1$, while the Lagrangian dual value is $0$.

Write $x=(u,v,r,z)\in\mathbb R^4$ and let $\ell(x)=\sqrt2\,u+v$. Define

$$
\begin{aligned}
K&=\{(u,v,r,z):0\le z\le1,\ r\ge0,\ \ell(x)\ge0,\\
&\hspace{7em}(1-z)^2\le r\ell(x)\},\\
X&=K\cap\mathbb Z^4.
\end{aligned}
$$ (eq-lagrangian-duality-gap-construction)

The objective is to minimize $z$, subject to the two additional constraints
$u\le0$ and $v\le0$. Put $P=\{x:u\le0,\ v\le0\}$, and define

$$
\begin{aligned}
v_{\rm int}&=\inf_{x\in X\cap P}z,\\
v_{\rm conv}&=\inf_{x\in\operatorname{conv}(X)\cap P}z,\\
v_{\rm cl}&=\inf_{x\in\overline{\operatorname{conv}(X)}\cap P}z.
\end{aligned}
$$ (eq-lagrangian-duality-gap-primal-values)

For $\lambda=(\lambda_1,\lambda_2)\in\mathbb R^2_+$, the Lagrangian and its dual are

$$
G(\lambda)=\inf_{x\in X}\bigl(z+\lambda_1u+\lambda_2v\bigr),
\qquad v^L=\sup_{\lambda\in\mathbb R^2_+}G(\lambda).
$$ (eq-lagrangian-duality-gap-dual)

```{prf:theorem} A gap of one
:label: thm-lagrangian-duality-gap

The set $K$ is closed and convex. Each of the three primal problems attains its
minimum, and

$$
v_{\rm int}=v_{\rm conv}=v_{\rm cl}=1,
\qquad \inf_{x\in X}z=0.
$$

For every nonnegative multiplier $\lambda$,

$$
G(\lambda)=
\begin{cases}
0,&\lambda=t(\sqrt2,1)\text{ for some }t\ge0,\\
-\infty,&\text{otherwise}.
\end{cases}
$$

In particular, $v^L=0<1=v_{\rm cl}$.
```

```{prf:proof}
The inequalities defining $K$ are closed conditions. Its last three conditions
say that the symmetric matrix

$$
\begin{pmatrix}r&1-z\\1-z&\ell(x)\end{pmatrix}
$$

is positive semidefinite. Hence $K$ is convex as well as closed. The Lean proof
establishes convexity directly through a weighted quadratic inequality.

If $x\in K\cap P$, then $\ell(x)\le0$ because $u,v\le0$, while membership in $K$
gives $\ell(x)\ge0$. Both coefficients in $\sqrt2\,u+v$ are positive, so $u=v=0$.
The inequality $(1-z)^2\le r\ell(x)$ then forces $z=1$. Thus
$K\cap P=\{(0,0,r,1):r\ge0\}$.

Since $K$ is closed and convex and contains $X$, it contains both
$\operatorname{conv}(X)$ and its closure. Consequently every feasible point in
each primal problem has objective value $1$. The point $(0,0,0,1)\in X\cap P$
attains that value in all three problems. Before imposing $P$, the objective is
nonnegative on $X$ and equals zero at $(1,0,1,0)\in X$.

The projection of the $z=0$ layer of $X$ onto its first two coordinates is exactly

$$
L=\{(u,v)\in\mathbb Z^2:\sqrt2\,u+v>0\}.
$$

Indeed, a point in this layer satisfies $1\le r(\sqrt2\,u+v)$, so the linear form
is positive. Conversely, for any $(u,v)\in L$, choose the integer
$r=\lceil1/(\sqrt2\,u+v)\rceil$ to obtain a point of $X$ with $z=0$.

Suppose first that $\lambda=t(\sqrt2,1)$ with $t\ge0$. The Lagrangian is
$z+t\ell(x)\ge0$ on $X$. Irrationality of $\sqrt2$ makes the additive subgroup
$\sqrt2\mathbb Z+\mathbb Z$ dense in $\mathbb R$, so there are positive values
$\sqrt2\,u+v$ arbitrarily close to zero. Lifting these lattice points to the
$z=0$ layer gives Lagrangian values arbitrarily close to zero (also for $t=0$).
Hence $G(\lambda)=0$.

For a nonnegative multiplier off that ray, there is an integer direction
$d=(d_1,d_2)$ with $(\sqrt2,1)\cdot d>0$ and $\lambda\cdot d<0$. To see this,
when $\lambda_2=0$ use $d=(-1,2)$. Otherwise choose a rational number $p/q$,
with $q>0$, strictly between $\lambda_1/\lambda_2$ and $\sqrt2$. If the ratio is
smaller than $\sqrt2$, use $d=(q,-p)$; if it is larger, use $d=(-q,p)$.
Every positive integer multiple $kd$ lifts to a point of the $z=0$ layer.
Its Lagrangian value is $k\lambda\cdot d$, which tends to $-\infty$.

This proves the stated formula for $G$. The ray includes the zero multiplier,
so its supremum over nonnegative multipliers is $0$.
```

The extra coordinate $r$ explains why closure does not close the gap. On the
$z=0$ layer, approaching the boundary $\ell(x)=0$ requires
$r\ge1/\ell(x)\to\infty$. These points cannot converge to a finite feasible
point of cost zero, although the Lagrangian ignores $r$.

In the formal statement below, `Kset`, `Xset`, and `Z` denote $K$, $X$, and the
objective $z$. `HasMinimumValue` asserts a lower bound together
with an attaining point. `IsInfimumOn` asserts a lower bound and arbitrarily
close objective values; `UnboundedBelowOn` supplies a point below every real
bound. `OnIrrationalRay` means $\lambda=t(\sqrt2,1)$ for some $t\ge0$.
Thus the last two conjuncts give the dual-function formula and a multiplier
with finite infimum zero, from which the dual value follows.

```{literalinclude} ../../lean/Lemmata/LagrangianDualityGap/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

The construction and proof are adapted from the Geoffrion theorem experiment,
specifically `formalizations/theorem14-multirow/Theorem14Counterexample.lean`
and its accompanying multirow report, at source revision
`e6c64b90ba8b15f4939e9650a13742c39c893efa`.

```{include} ../_generated/verification/lagrangian-duality-gap.md
```
