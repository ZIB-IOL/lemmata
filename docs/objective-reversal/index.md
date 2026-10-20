---
title: Objective reversal and near-exact approximation
---

```{include} ../_generated/provenance/objective-reversal.md
```

Replacing a maximization objective $v$ by $N-v$ preserves exact
optimization, but changes multiplicative approximation guarantees. This entry
gives the optimum and slack calculations needed to transfer lower bounds
through such a replacement. The source nonnegative-rank lower bound and the
combinatorial maps are explicit inputs.

```{prf:definition} Objective reversal with completion
:label: def-objective-reversal

Let $I$ be an instance set, $S$ a source solution set, and $T$ a target
solution set. Let $v_i(s)$ be a source value, $c_i(t)$ a target cost,
and $b_i$ a baseline. An objective reversal consists of maps
$g:S\to T$ and $h:T\to S$, both independent of $i$, such that
for every $i,s,t$,
$$
c_i(g(s))=b_i-v_i(s),\qquad c_i(g(h(t)))\le c_i(t).
$$
The second condition says that completion to an encoded source solution
does not increase the target cost.
```

```{prf:theorem} Transfer of the optimum
:label: thm-objective-reversal-optimum

Suppose an objective reversal is given. Fix an instance $i$, and let
$o\in\mathbb R$ satisfy $v_i(s)\le o$ for every $s\in S$, with equality
for at least one source solution. Then
$$
c_i(t)\ge b_i-o\quad\text{for every }t\in T,
$$
and equality holds for at least one target solution.
```

```{prf:proof} of [](#thm-objective-reversal-optimum)
:nonumber:

For any target solution $t$,
$c_i(t)\ge c_i(g(h(t)))=b_i-v_i(h(t))\ge b_i-o$.
If $s$ attains the source maximum, $g(s)$ has cost $b_i-o$.
```

```{prf:lemma} Slack identity
:label: lem-objective-reversal-identity

For real $N,C,o,v$ and a nonzero real $\alpha$,
$$
C-v=
\left(N-v-\frac{N-o}{\alpha}\right)
+\left(C-o-\left(1-\frac1\alpha\right)(N-o)\right).
$$
In approximation applications $\alpha\ge1$. The Lean identity also holds
at zero under Lean's convention for division.
```

```{prf:proof} of [](#lem-objective-reversal-identity)
:nonumber:

Expand the second parenthesis. The terms containing
$(N-o)/\alpha$ cancel, leaving $C-v$.
```

```{prf:lemma} A nonnegative correction at the edge-cover scale
:label: lem-objective-reversal-offset

Let $N>0$, $o\ge0$, and $C-o\ge1/4$. Set
$\alpha=1+1/(4N)$. Then
$$
R=C-o-\left(1-\frac1\alpha\right)(N-o)\ge0.
$$
```

```{prf:proof} of [](#lem-objective-reversal-offset)
:nonumber:

We have $1-1/\alpha=1/(4N+1)$. Since $o\ge0$,
$$
\frac{N-o}{4N+1}\le\frac{N}{4N+1}<\frac14\le C-o.
$$
Subtracting the approximation loss gives the result.
```

```{prf:theorem} Transfer of a near-exact factorization
:label: thm-objective-reversal-factorization

Let an objective reversal be given with constant baseline $b_i=N>0$.
Suppose $o_i\ge0$ and $C_i-o_i\ge1/4$ for every instance $i$.
If the matrix
$$
M(i,t)=c_i(t)-\frac{N-o_i}{1+1/(4N)}
$$
has a nonnegative factorization with $k$ terms, then
$$
S(i,s)=C_i-v_i(s)
$$
has a nonnegative factorization with $k+1$ terms.

For the algebraic statement, the numbers $o_i$ need not be optima.
When they are attained source maxima, the optimum-transfer theorem shows
that $N-o_i$ is the corresponding target minimum.
```

```{prf:proof} of [](#thm-objective-reversal-factorization)
:nonumber:

Restrict the target factorization to columns $g(s)$. By the slack identity,
$S(i,s)=M(i,g(s))+R_i$, where the preceding lemma gives $R_i\ge0$.
The row-constant matrix $(R_i)_{i,s}$ has a one-term nonnegative
factorization. Append that term to the restricted factorization.
This is a special case of [](#thm-nonnegative-rank-reduction-factorization).
```

```{prf:corollary} Source lower bounds as inputs
:label: cor-objective-reversal-rank

Under the hypotheses of the preceding theorem, if
$r_+(S)\ge L$ for a natural number $L$, every $k$-term nonnegative
factorization of $M$ satisfies
$$
L\le k+1.
$$
```

```{prf:proof} of [](#cor-objective-reversal-rank)
:nonumber:

The constructed factorization bounds $r_+(S)$ by $k+1$. Combine this
upper bound with the assumed source lower bound.
```

For the metric edge-cover application on an even complete graph, the intended
data are source perfect matchings, target edge covers,
$v_H(M)=|M\cap E(H)|$, and costs $c^H_e=2-\mathbf1[e\in E(H)]$.
A separate combinatorial argument must supply an instance-independent
completion satisfying the definition above. The source matching lower bound
must also be supplied. This entry establishes the reduction calculation; it
does not formalize that completion or the matching lower-bound theorem.

The results are instances of the reduction framework in
[Braun–Pokutta–Zink, *Affine reductions for LPs and SDPs*](https://arxiv.org/abs/1410.8816)
and [Braun–Pokutta–Roy, *Strong reductions for extended formulations*](https://arxiv.org/abs/1512.04932).
For the additional passage from affine LP certificates to matrix
factorizations, see [](#thm-formulation-reduction-factorization).

The definitions and statements are separated from the proofs:

```{literalinclude} ../../lean/Lemmata/ObjectiveReversal/Statement.lean
:language: lean
```

```{literalinclude} ../../lean/Lemmata/ObjectiveReversal/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/objective-reversal.md
```
