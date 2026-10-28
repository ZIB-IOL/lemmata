---
title: MinRank Lower Bounds for the Cocubic Reed–Muller Covering Radius
---

```{include} ../_generated/provenance/cocubic-covering.md
```

The Reed–Muller code $\mathrm{RM}(r,m)$ consists of the Boolean polynomials in $m$ variables of degree at most $r$. The distance of a polynomial $f$ to this code is the minimum weight in the coset $f+\mathrm{RM}(r,m)$, where $\operatorname{wt}(g)=|\{x:g(x)=1\}|$. Maximizing this distance over $f\in\mathrm{RM}(s,m)$ gives the relative covering radius

$$
\rho\bigl(\mathrm{RM}(r,m),\mathrm{RM}(s,m)\bigr)
=\max_{f\in\mathrm{RM}(s,m)}\min_{h\in\mathrm{RM}(r,m)}\operatorname{wt}(f+h).
$$

We study the cocubic case $r=m-4$, $s=m-3$. A lower bound requires one polynomial $f$ for which every member of the coset has large weight. We obtain such bounds by associating an affine family of alternating matrices to $f$ and bounding its minimum rank.

## Previous lower bounds

@dougherty2022covering proved the lower bound $\rho(\mathrm{RM}(5,9),\mathrm{RM}(6,9))\ge28$ and the constructive bound $\rho(\mathrm{RM}(m-4,m),\mathrm{RM}(m-3,m))\ge2m+10$ for $m\ge8$. We recall the self-orthogonality construction underlying these bounds.

Work over $\mathbb F_2$, and fix a Boolean polynomial $f$ in $m\ge4$ variables with $\deg f=m-3$. Write a correction $h\in\mathrm{RM}(m-4,m)$ as $h=p+\ell$, where $p$ is its homogeneous degree-$(m-4)$ part and $\ell$ contains the lower-degree terms. Put $g=f+h$, $S=\{x\in\mathbb F_2^m:g(x)=1\}$ and $n=|S|=\operatorname{wt}(g)$.

Evaluating a polynomial on the $n$ points of $S$ gives a vector in $\mathbb F_2^n$. Let $V_g$ be the span of the value vectors of $g,x_1g,\ldots,x_mg$. Since $g=1$ on $S$, these are also the value vectors of $1,x_1,\ldots,x_m$.

The dot product of the evaluation vectors of affine polynomials $a,b$ is

$$
\sum_{x\in S}a(x)b(x)
=\sum_{x\in\mathbb F_2^m}a(x)b(x)g(x)=0,
$$

because $\deg(abg)\le m-1$ and every Boolean polynomial of degree less than $m$ has zero total sum. Thus $V_g\subseteq V_g^\perp$ in the $n$-dimensional space $\mathbb F_2^n$, giving the initial bound $n\ge2\dim V_g$.

In their construction, quadratic multiples strengthen this bound. Let $Q_f$ be the space of homogeneous quadratic polynomials $q$ satisfying $\deg(qf)\le m-2$. Then $\deg(qg)\le m-2$, so the value vector of $q$ is orthogonal to $V_g$.

Their certificates select $k$ quadratic multiples whose value vectors are mutually orthogonal and independent modulo $V_g$. Together with the linear independence of the affine value vectors, this gives $n\ge2m+2k+2$. Different choices of multipliers handle different correction coefficients. Here we bound the rank of the pairing on the whole space $Q_f$, turning the quadratic contribution into an affine MinRank problem.

## The MinRank method

For $q,q'\in Q_f$, define their pairing by

$$
b_p(q,q')=\sum_{x\in S}q(x)q'(x)
=\sum_{x\in\mathbb F_2^m}q(x)q'(x)(f+p)(x).
$$

The lower-degree term $\ell$ disappears from this sum because $qq'\ell$ has degree less than $m$. Also $b_p(q,q)=\sum_xq(x)g(x)=0$, so $b_p$ is alternating. Its matrix in a fixed basis of $Q_f$ depends affinely on the coefficients of $p$.

::::{prf:theorem}
:label: thm-cocubic-covering-weight

Every $g=f+h$ with $\deg h\le m-4$ satisfies $\operatorname{wt}(g)\ge2\dim V_g+\operatorname{rank}b_p$.

::::

::::{prf:proof} of [](#thm-cocubic-covering-weight)
:nonumber:

Choose $q_1,\ldots,q_t$ such that the functionals $b_p(q_i,\cdot)$ are independent, where $t=\operatorname{rank}b_p$. Their evaluation vectors are independent modulo $V_g$: pairing any relation with the value vector of each $q\in Q_f$ gives the same relation among these functionals. These vectors lie in $V_g^\perp$, so $\dim V_g+t\le\dim V_g^\perp=n-\dim V_g$.

::::

If the degree-$(m-2)$ parts of $x_1f,\ldots,x_mf$ are linearly independent, then the affine value vectors are linearly independent for every correction and $\dim V_g=m+1$. The theorem then gives $\operatorname{wt}(g)\ge2m+2+\operatorname{rank}b_p$, reducing a coset-weight lower bound to an affine MinRank lower bound.

Under this independence hypothesis, a level-$k$ certificate in the sense of @dougherty2022covering exists if and only if $\operatorname{rank}b_p\ge2k$ for every $p$, when certificate size is unrestricted. Both formulations give the weight lower bound $2m+2k+2$.

To reduce the matrix family, choose a subspace $N\subseteq Q_f$ so that the restriction $A_p$ of $b_p$ to $N$ depends on only a small linear projection of $p$. Its possible values can then be enumerated while the other coefficients remain free. For each value, put $A_p$ into symplectic normal form and let $C_p$ be the pairing between $\operatorname{rad}A_p$ and the remaining coordinates.

Splitting off the nonsingular part of $A_p$ contributes $\operatorname{rank}A_p$ and leaves a matrix of the form $\begin{pmatrix}0&C_p\\C_p^\top&D_p\end{pmatrix}$. A nonsingular submatrix of $C_p$ gives a nonsingular principal submatrix of twice the size in this matrix. Hence

$$
\operatorname{rank}b_p\ge\operatorname{rank}A_p+2\operatorname{rank}C_p.
$$

To prove $\operatorname{rank}C_p\ge t$, choose a $t$-dimensional subspace $H\subseteq\operatorname{rad}A_p$. If $\operatorname{rank}C_p<t$, some nonzero $u\in H$ satisfies $u^\top C_p=0$. There are $2^t-1$ choices for $u$, and each gives linear equations in the remaining coefficients of $p$. Gaussian elimination either closes a branch or records a new kernel direction. Repeating this argument modulo the directions already found gives a search over possible low-rank completions. Symmetries of the matrix family identify equivalent branches.

## Lower bounds

For $m=9,10,11$, let

$$
\begin{aligned}
F_m={}&x_1x_4x_7+x_1x_5x_8+x_1x_6x_9+x_2x_4x_8+x_2x_5x_7+x_2x_5x_9\\
&+x_2x_6x_7+x_3x_4x_9+x_3x_5x_7+x_3x_6x_8+x_3x_6x_9+x_{m-2}x_{m-1}x_m.
\end{aligned}
$$

Let $f_m$ be the cocubic polynomial obtained from $F_m$ by replacing each cubic monomial with the product of the other $m-3$ variables.

For each form, the degree-$(m-2)$ parts of $x_1f_m,\ldots,x_mf_m$ are linearly independent. For $g=f_m+h$, if an affine polynomial $a$ vanishes on $S=\operatorname{supp}(g)$, then $ag=0$. Its degree-$(m-2)$ part forces the linear coefficients of $a$ to vanish, and $\deg g=m-3$ then forces its constant coefficient to vanish. Thus the affine value vectors are linearly independent and $\dim V_g=m+1$ for every correction.

We apply the local rank reduction to the three forms. The calculations for $m=10,11$ exclude rank at most $8$; the nine-variable calculation excludes rank at most $10$, using polynomial identities for the remaining branches. Since $b_p$ is alternating, these exclusions give the rank bounds below. Combining them with [](#thm-cocubic-covering-weight) gives the corresponding weight bounds.

::::{prf:lemma}
:label: lem-cocubic-covering-nine

For $f=f_9$ and every $h\in\mathrm{RM}(5,9)$, we have $\operatorname{rank}b_p\ge12$ and $\operatorname{wt}(f+h)\ge32$.

::::

::::{prf:lemma}
:label: lem-cocubic-covering-ten

For $f=f_{10}$ and every $h\in\mathrm{RM}(6,10)$, we have $\operatorname{rank}b_p\ge10$ and $\operatorname{wt}(f+h)\ge32$.

::::

::::{prf:lemma}
:label: lem-cocubic-covering-eleven

For $f=f_{11}$ and every $h\in\mathrm{RM}(7,11)$, we have $\operatorname{rank}b_p\ge10$ and $\operatorname{wt}(f+h)\ge34$.

::::

The known upper bound $32$ of @dougherty2022covering therefore gives $\rho(\mathrm{RM}(5,9),\mathrm{RM}(6,9))=32$. The upper bound $32$ of @khoruzhii2026weight similarly gives $\rho(\mathrm{RM}(6,10),\mathrm{RM}(7,10))=32$.

The three consecutive examples also give a uniform construction in higher dimensions. The three-variable extension of @dougherty2022covering replaces $f(x)$ by $f^*(x,y)=y_1y_2y_3f(x)+x_1\cdots x_m$. The rank lower bound for the old quadratic multipliers and the independence of affine multiples are preserved, so each step increases the resulting weight lower bound by $6$. Starting from $m=9,10,11$ therefore gives $\rho(\mathrm{RM}(m-4,m),\mathrm{RM}(m-3,m))\ge2m+12$ for every $m\ge9$, improving their constructive bound $2m+10$.

The cubic-form catalog is described by @khoruzhii2026classification; reference implementations of the lower-bound searches and accompanying data are available in the [BCF10 repository](https://github.com/khoruzhii/bcf10).


```{literalinclude} ../../lean/Lemmata/CocubicCovering/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/cocubic-covering.md
```
