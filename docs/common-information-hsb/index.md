---
title: Common information and hyperplane separation are incomparable
---

```{include} ../_generated/provenance/common-information-hsb.md
```

Two explicit matrix families separate common information from the logarithm of
HSB in both directions. This gives a negative answer to the literal polynomial
comparison in @braun2017information, Question 7.2, for the unmodified
functionals on a fixed matrix. No claim about comparisons optimized over
rescalings, representations, or conditioning is intended.

## The functionals

Throughout, $M$ is a finite, entrywise nonnegative, nonzero real matrix. Write
$Z=\sum_{i,j}M_{ij}>0$ and $P=M/Z$. Information quantities on this page are in
**bits**, with $0\log_2 0=0$.

```{prf:definition} Finite common information
:label: def-common-information-hsb-ci

A finite product seed consists of an arbitrary positive integer $k$, probability
weights $w_z$, and probability vectors $p_z,q_z$, satisfying

$$
 P_{ij}=\sum_{z=1}^k w_z p_z(i)q_z(j).
$$ (eq-common-information-hsb-mixture)

The common information of $M$ is

$$
 \mathbb C[M]=\inf_{k,w,p,q}
 \left\{H_2(P)-\sum_{z=1}^k w_z\bigl(H_2(p_z)+H_2(q_z)\bigr)\right\}.
$$ (eq-common-information-hsb-ci)

The infimum ranges over **all finite product mixtures**, not only uniform
rectangle mixtures. Zero entries and zero-weight components are permitted.
```

This is the finite-auxiliary characterization of Wyner common information [@wyner1975common],
used for matrix lower bounds by @braun2013common. The joint distribution
$\Pr[\Pi=z,A=i,B=j]=w_zp_z(i)q_z(j)$ makes $A,B$ conditionally independent given
$\Pi$, and its displayed cost is $I((A,B);\Pi)$, **not** $H_2(\Pi)$.
Conversely, any finite joint law with conditional independence yields such a
seed. At a zero-mass seed value, arbitrary probability marginals may be chosen.
Both directions, preservation of the full joint law, and the mutual-information
identity are represented in `Seeds.lean` and `JointSeeds.lean`.

Internally, `entropy` and `commonInformationNat` use natural logarithms;
`commonInformation` divides by $\log 2$. The deterministic pair seed makes the
cost set nonempty, and entropy concavity makes every cost nonnegative. Thus the
infimum is well defined on the stated domain. Positive global scaling does not
change $P$ or common information. A product distribution has zero common
information even if an unnecessarily randomized seed has positive entropy.

```{prf:proposition} Relation to nonnegative rank
:label: prop-common-information-hsb-rank

The nonnegative rank of $M$ is a positive finite integer $k$, and

$$
 2^{\mathbb C[M]}\le k=\operatorname{rank}_+(M).
$$ (eq-common-information-hsb-rank)
```

```{prf:proof} of [](#prop-common-information-hsb-rank)
:nonumber:
Normalize each nonzero outer-product factor to a product distribution, assigning
it weight equal to its mass divided by $Z$. Zero factors receive weight zero and
arbitrary probability marginals. The resulting seed has cost at most its entropy,
which is at most $\log_2 k$. Finite nonnegative matrices admit a factorization,
and the least feasible integer factor count is attained. Applying the construction
to that least count proves the claim; an infimum inequality in the opposite
direction would not suffice. The nonnegative-rank definition is reused from the
[spanning-tree factorization entry](../spanning-tree-min-split/index.md).
```

```{prf:definition} Max-entry-normalized HSB
:label: def-common-information-hsb-hsb

Set $m_\infty=\max_{i,j}M_{ij}>0$. A real matrix $W$ is feasible if
$\sum_{i\in A,j\in B}W_{ij}\le1$ for every row set $A$ and column set $B$.
Define

$$
 \operatorname{HSB}(M)
 =\sup_{W\text{ feasible}}\frac{\sum_{i,j}W_{ij}M_{ij}}{m_\infty}.
$$ (eq-common-information-hsb-hsb)

Witness entries may be **negative**. Constraints apply to every rectangle, not
only rectangles contained in the support of $M$.
```

The zero witness gives a nonempty feasible set. Singleton constraints imply
$W_{ij}\le1$, so the objective is bounded above by $Z/m_\infty$. A singleton
witness at a maximum entry gives $\operatorname{HSB}(M)\ge1$. Positive global
scaling leaves HSB unchanged. These facts and the exact family values below are
proved directly; no linear-programming duality assumption is used.

## Exact separating families

```{prf:theorem} Half-heavy diagonal
:label: thm-common-information-hsb-diagonal

For every integer $N\ge1$, let

$$
 D_N=\operatorname{diag}\left(\frac12,
             \underbrace{\frac1{2N},\ldots,\frac1{2N}}_{N\text{ entries}}\right).
$$ (eq-common-information-hsb-diagonal)

Then

$$
 \mathbb C[D_N]=1+\tfrac12\log_2 N,
 \qquad \operatorname{HSB}(D_N)=2.
$$ (eq-common-information-hsb-diagonal-values)
```

```{prf:proof} of [](#thm-common-information-hsb-diagonal)
:nonumber:
Every positive-weight product component supported on a diagonal is a point mass.
Its conditional entropy is zero, so every admissible seed has cost equal to the
entropy of the diagonal distribution. The displayed entropy follows directly.
For HSB, singleton constraints give the upper bound
$(\sum_iD_{ii})/\max_iD_{ii}=2$. The witness with diagonal entries $1$ and
off-diagonal entries $-1$ attains it: its sum on $A\times B$ is
$2|A\cap B|-|A||B|\le1$. Zero-weight seed components need not themselves be
supported on the diagonal; the proof does not impose that false restriction.
```

```{prf:theorem} A large product block and singleton blocks
:label: thm-common-information-hsb-blocks

For integers $S\ge1$ and $r\ge0$, let $B_{S,r}=J_S\oplus I_r$, where $J_S$
is the $S\times S$ all-ones matrix. Put

$$
 w=\frac{(S^2,\underbrace{1,\ldots,1}_{r\text{ entries}})}{S^2+r}.
$$ (eq-common-information-hsb-block-weights)

Then

$$
 \mathbb C[B_{S,r}]=H_2(w),
 \qquad \operatorname{HSB}(B_{S,r})=r+1.
$$ (eq-common-information-hsb-block-values)

There are $r+1$ nonempty blocks, including when $r=0$.
```

```{prf:proof} of [](#thm-common-information-hsb-blocks)
:nonumber:
The seed revealing the block and choosing the two coordinates independently
and uniformly inside that block attains $H_2(w)$. For the converse, every
positive-weight product component is confined to one block. Its entropy is
at most the logarithm of that block's number of entries. Summing these bounds
with the required block masses gives cost at least $H_2(w)$ for **every** finite
product seed. This does not assert uniqueness of the seed.

One unit rectangle per block gives the HSB upper bound $r+1$. For a matching
witness, select one coordinate in each block, put the signed diagonal witness
from the preceding proof on those selected coordinates, and put zero elsewhere.
Every rectangle sum reduces to a rectangle sum of that signed witness, while
the objective is $r+1$ and the maximum entry is one.
```

## Quantified incomparability

```{prf:corollary} Unbounded information at fixed HSB
:label: cor-common-information-hsb-fixed

For every $L\in\mathbb R$, there is $N\ge1$ with
$\mathbb C[D_N]>L$ and $\operatorname{HSB}(D_N)=2$.
```

```{prf:corollary} Large logarithmic HSB at small information
:label: cor-common-information-hsb-small

For every $L\in\mathbb R$ and $\varepsilon>0$, there are integers $r\ge0$,
$S\ge1$ such that

$$
 \log_2\operatorname{HSB}(B_{S,r})>L,
 \qquad \mathbb C[B_{S,r}]<\varepsilon.
$$ (eq-common-information-hsb-small)
```

```{prf:proof} of [](#cor-common-information-hsb-fixed) and [](#cor-common-information-hsb-small)
:nonumber:
The diagonal entropy diverges with $N$. For the second statement, first choose
$r$ with $\log_2(r+1)>L$, and only then let $S$ grow. With this fixed $r$, the
large block's mass tends to one and each singleton mass tends to zero.
Continuity of $-x\log x$ at zero and one gives $H_2(w)\to0$.
```

```{prf:theorem} No polynomial comparison
:label: thm-common-information-hsb-polynomial

For every $a\ge0$ and integer $d\ge0$, there are matrices violating each of

$$
 \mathbb C[M]\le a\bigl(1+\log_2\operatorname{HSB}(M)\bigr)^d,
 \qquad
 \log_2\operatorname{HSB}(M)\le a\bigl(1+\mathbb C[M]\bigr)^d.
$$ (eq-common-information-hsb-polynomial)

The first violation is a half-heavy diagonal, the second a block matrix.
```

```{prf:proof} of [](#thm-common-information-hsb-polynomial)
:nonumber:
For the diagonal family the proposed right side is the fixed number $a2^d$.
For the reverse direction, choose common information below one and logarithmic
HSB above $a2^d$. Nonnegativity of common information gives
$a(1+\mathbb C[M])^d\le a2^d$. These polynomial-growth majorants include bounds
by any fixed polynomial on nonnegative arguments.
```

## Scope

The result concerns the raw, fixed-matrix evaluations in the definitions above.
It does not compare methods after optimizing row/column rescaling, choosing
submatrices, or imposing additional conditioning. In particular, small positive
CI approaching zero does not by itself refute every arbitrary comparison
function that might be unbounded near zero. No such stronger claim, geometric
realization of these matrices, or novelty/priority assertion is made here.

The formalization covers finite auxiliary alphabets and their exact finite-joint
interpretation; it does not separately formalize a reduction from arbitrary
auxiliary probability spaces. The sources [@wyner1975common; @braun2013common; @braun2017information]
supply the historical context. Question 7.2 in @braun2017information asks the comparison
question; it does not prove the
incomparability established by the displayed families.

```{literalinclude} ../../lean/Lemmata/CommonInformationHsb/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/common-information-hsb.md
```
