---
title: LP hardness of approximation for polynomial-time solvable problems
---

```{include} ../_generated/provenance/lp-hardness-in-p.md
```

Polynomial-time optimization does not imply the existence of a small LP
formulation. This contribution gives approximation-preserving reductions
for four problems: minimum-cost perfect matching, minimum-cost $T$-join,
minimum odd cut, and minimum-cost odd-red bipartite perfect matching.
Each problem admits an exact polynomial-time algorithm. Nevertheless,
shifted matching matrices yield strong lower bounds on a common LP
formulation supporting all objectives.

We give the four applications together with the factorization argument
that underlies them. The Lean development includes the actual graph and
matching domains, objective sums, attaining solutions, and reductions.
The published matching-matrix rank bound is an explicit theorem hypothesis.
For parity matching, Lean also proves the new finite extension of the
rectangle argument, from explicitly stated hypotheses describing the
Jia–Svensson–Yuan partition framework. No external theorem is introduced
as a Lean axiom.

For every fixed $\alpha>1$, the implications are as follows.
Here $n$ is the number of vertices in the first three rows and the number
of vertices in each bipartition class in the last row.

| Problem | Restricted objectives | Lower bound on LP size | Nonnegative-rank lower bound used |
| --- | --- | --- | --- |
| Minimum-cost perfect matching | Strictly positive metric costs on $K_n$ | $2^{\Omega_\alpha(n)}$ | Shifted ordinary matching matrix |
| Minimum-cost $T$-join | $T=V(K_n)$, the same metric costs | $2^{\Omega_\alpha(n)}$ | Shifted ordinary matching matrix |
| Minimum odd cut | Weights in $\{0,1\}$ on $K_n$ | $2^{\Omega_\alpha(n)}$ | Transpose of the shifted ordinary matching matrix |
| Minimum-cost odd-red bipartite perfect matching | Positive costs on a fixed two-colored complete bipartite multigraph | $2^{\Omega_\alpha(n)}$ | Shifted parity-matching matrix |

The first three applications use the exponential nonnegative-rank bound
for the shifted odd-cut versus perfect-matching matrix proved by
@braun2014matching. The fourth uses a
different matrix, from
@jia2022exact. Their published
exact bound alone does not give the shift needed for a fixed-factor
approximation. Below we prove the required extension; Lean checks its
new construction, charging estimate, and finite rank consequence, while
their partition and entropy assertions remain explicit hypotheses.

## Formulations and source matrices

Fix a set $I$ of instances, a set $X$ of solutions, and objective values
$v(i,x)$. An $\alpha$-approximate formulation for this minimization problem
has one polyhedron $P$, with $m$ inequalities, a realization $z_x\in P$ for
every solution, and an affine objective $\ell_i$ for each instance such that

$$
\ell_i(z_x)=v(i,x),\qquad
\inf_{z\in P}\ell_i(z)\ge \frac{\operatorname{OPT}(i)}{\alpha}.
$$

Both $P$ and the realization $x\mapsto z_x$ are independent of the instance.
The encoding is otherwise arbitrary. Equations can be removed by
parametrizing their affine solution space and do not count toward $m$.
The lower bounds concern this model, which allows arbitrary extended
formulations. They do not bound the running time of an algorithm. For the
usual rational-input model, it suffices to use a fixed rational approximation
factor: hardness for any rational factor larger than a given real $\alpha$
also rules out an $\alpha$-approximate formulation. The resulting cost
families have rational entries of polynomial encoding length.

Write $r_+(S)$ for the nonnegative rank of a real matrix $S$: the least
number of nonnegative rank-one summands, or $\infty$ if no finite
factorization exists. The Lean definition is shared with the
[spanning-tree contribution](../spanning-tree-min-split/index.md).

For even $n$, let $\mathcal U_n$ be the odd subsets of $[n]$ and let
$\mathcal M_n$ be the perfect matchings of $K_n$. Set

$$
q_n(U,M)=|\delta(U)\cap M|,
\qquad
Q_{n,r}(U,M)=q_n(U,M)-r.
$$

The theorem of Braun and Pokutta used here states that

$$
r_+(Q_{n,r})=2^{\Omega_r(n)}
\quad\text{for every fixed }0<r<1.
$$ (eq-lp-hardness-in-p-matching-source)

In Section 2.2.3 and the proof of Theorem 3.1 of
@braun2014matching, the relevant
submatrix has entries $(q_n-1+\beta)/2$ for fixed $0<\beta<1$.
Taking $\beta=1-r$ and rescaling gives the stated nonnegative-rank bound.
The exact matching bound of @rothvoss2013matching
corresponds to $r=1$; it is not by itself a bound for $r<1$.

We use the formulation-complexity factorization theorem in its usual
affine Farkas form, as in
@braun2014affine and
@braun2015strong.
For precision, the formalization starts from the certificate data:
if $P=\{z:s_l(z)\ge0,\ 1\le l\le m\}$ and $\beta_i$ is the claimed
objective bound, it assumes nonnegative coefficients $y_{il},\kappa_i$
with

$$
\ell_i(z)-\beta_i
=\sum_{l=1}^m y_{il}s_l(z)+\kappa_i
\quad\text{for all }z.
$$

The Lean structure `CertifiedLP` contains the inequalities, feasible
realizations, exact objective values, and this identity.
The existence of these certificates from validity on a finite-dimensional
polyhedron is the external affine Farkas theorem.

```{prf:theorem} Factorization from affine certificates
:label: thm-lp-hardness-in-p-factorization

The slack matrix $S(i,x)=v(i,x)-\beta_i$ of a certified formulation
with $m$ inequalities has a nonnegative factorization with $m+1$ terms.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-factorization)
:nonumber:

Evaluate the certificate at each feasible realization:

$$
S(i,x)=\sum_{l=1}^m y_{il}s_l(z_x)+\kappa_i\cdot1.
$$

All factors are nonnegative. The constant term accounts for the possible
additional factor.
```

In each application below, $L$ is a nonnegative integer. A source bound
$L\le r_+(S)$ therefore
gives $L\le m+1$. Substituting an exponential source bound gives the
corresponding exponential lower bound on formulation size.

## Minimum-cost perfect matching

Let $n\ge2$ be even, put $H=n/2$, and fix $\alpha>1$. For $U\in\mathcal U_n$
give the edges of $K_n$ costs

$$
c^U_e=1+\lambda\,\mathbf1[e\in\delta(U)],
\qquad \lambda=(\alpha-1)n=2(\alpha-1)H.
$$

```{prf:proposition} Cut metrics
:label: prop-lp-hardness-in-p-metric

For any vertex set, map $b:V\to\{0,1\}$, and $\gamma\ge0$, the distances
$d(u,u)=0$ and
$d(u,v)=1+\gamma\,\mathbf1[b(u)\ne b(v)]$ for $u\ne v$ are nonnegative,
symmetric, strictly positive off the diagonal, and satisfy the triangle
inequality.
```

```{prf:proof} of [](#prop-lp-hardness-in-p-metric)
:nonumber:

If two endpoints have different labels, at least one of the two edges
through an intermediate vertex joins different labels. If the endpoints
have the same label, their distance is one. These observations prove the
triangle inequality, including the cases of repeated vertices.
```

In particular, $c^U$ is a strictly positive metric. It is also a tree
metric: attach each vertex to its side's center by an edge of length
$1/2$, and join the centers by an edge of length $\lambda$.

```{prf:lemma} Matching optimum
:label: lem-lp-hardness-in-p-matching-optimum

For every odd $U$, every perfect matching has cost at least $H+\lambda$,
and some perfect matching attains $H+\lambda$.
```

```{prf:proof} of [](#lem-lp-hardness-in-p-matching-optimum)
:nonumber:

Every perfect matching has $H$ edges and crosses every odd cut.
Choose one vertex in $U$ and one outside $U$, match these two vertices,
and pair the remaining vertices within their respective sides. Both
remaining sets have even size. This constructs a matching with exactly
one crossing. Hence
$c^U(M)=H+\lambda q_n(U,M)$ has minimum $H+\lambda$.
```

```{prf:theorem} LP lower bound for metric minimum-cost perfect matching
:label: thm-lp-hardness-in-p-matching

Let $L\in\mathbb N$ satisfy $L\le r_+(Q_{n,1/(2\alpha)})$.
Every certified $\alpha$-approximate formulation for the above metric
minimum-cost perfect matching instances, with $m$ inequalities, satisfies
$L\le m+1$.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-matching)
:nonumber:

The approximation slack is exactly

$$
c^U(M)-\frac{\operatorname{OPT}(U)}{\alpha}
=H+\lambda q_n(U,M)-\frac{H+\lambda}{\alpha}
=\lambda\left(q_n(U,M)-\frac1{2\alpha}\right).
$$

Since $\lambda>0$, scaling preserves nonnegative rank. Apply
[](#thm-lp-hardness-in-p-factorization).
```

Applying the bound $r_+(Q_{n,r})=2^{\Omega_r(n)}$ of
@braun2014matching with $r=1/(2\alpha)$
gives $m=2^{\Omega_\alpha(n)}$ for every fixed $\alpha>1$, although
weighted perfect matching is polynomial-time
solvable. The costs are $1$ and $1+(\alpha-1)n$. Thus their aspect ratio
grows with $n$; this is not a bounded-aspect-ratio claim.

## Minimum-cost $T$-join

Again let $n\ge2$ be even and take $T=V(K_n)$.
A $T$-join is an edge set $J$ whose odd-degree vertex
set is $T$. Use the same costs $c^U$.

```{prf:lemma} $V$-join optimum
:label: lem-lp-hardness-in-p-join-optimum

For every odd $U$, every $V$-join costs at least $H+\lambda$, and some
$V$-join attains this value.
```

```{prf:proof} of [](#lem-lp-hardness-in-p-join-optimum)
:nonumber:

Every degree in $J$ is at least one, so the degree-sum identity gives
$|J|\ge n/2=H$. Every odd cut contains an edge of $J$: otherwise the
graph induced by $U$ would have odd degree at all its vertices, whereas
a graph has an even number of odd-degree vertices. Therefore

$$
c^U(J)=|J|+\lambda|J\cap\delta(U)|\ge H+\lambda.
$$

A one-crossing perfect matching is a $V$-join attaining equality.
```

```{prf:theorem} LP lower bound for minimum-cost $T$-join
:label: thm-lp-hardness-in-p-join

Let $L\le r_+(Q_{n,1/(2\alpha)})$.
Every certified $\alpha$-approximate formulation for the above
minimum-cost $V$-join instances, with $m$ inequalities, satisfies
$L\le m+1$.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-join)
:nonumber:

Restrict the realization map to perfect matchings, each regarded as a
$V$-join. This inclusion is independent of $U$. The optimum is still
$H+\lambda$, and the restricted slack is exactly the matching slack
in [](#thm-lp-hardness-in-p-matching). Restricting columns cannot increase
nonnegative rank.
```

Thus minimum-cost $T$-join has formulation size
$2^{\Omega_\alpha(n)}$ already for $T=V(K_n)$ and these positive metric
costs. Minimum-cost $T$-join is polynomial-time solvable, for example
through shortest-path distances and minimum-weight perfect matching
on $T$.

## Minimum odd cut

Let $n\ge2$ be even. The solutions are now odd subsets $U$ of $[n]$.
Each perfect matching
$M$ specifies an objective with edge weights $w^M_e=\mathbf1[e\in M]$.
The cost of the cut is $q_n(U,M)$.

```{prf:lemma} Odd-cut optimum
:label: lem-lp-hardness-in-p-odd-cut-optimum

For every perfect matching $M$ on a nonempty vertex set, every odd cut
has weight at least one, and a singleton cut has weight one.
```

```{prf:proof} of [](#lem-lp-hardness-in-p-odd-cut-optimum)
:nonumber:

A perfect matching crosses every odd cut. A singleton cut contains
precisely the unique matching edge incident with its vertex.
```

```{prf:theorem} LP lower bound for minimum odd cut
:label: thm-lp-hardness-in-p-odd-cut

Let $L\le r_+(Q_{n,1/\alpha})$.
Every certified $\alpha$-approximate formulation for minimum odd cut
with the above $\{0,1\}$ weights, with $m$ inequalities, satisfies
$L\le m+1$.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-odd-cut)
:nonumber:

The slack, indexed by $M$ and $U$, is $q_n(U,M)-1/\alpha$.
It is the transpose of $Q_{n,1/\alpha}$. Transposition preserves
nonnegative rank, so apply [](#thm-lp-hardness-in-p-factorization).
```

The resulting bound is $2^{\Omega_\alpha(n)}$ for fixed $\alpha>1$.
Polynomial-time solvability is supplied by the odd-cut algorithm of
@padberg1982odd.

## Minimum-cost odd-red bipartite perfect matching

Let $G_n$ have left vertices $u_1,\ldots,u_n$ and right vertices
$v_1,\ldots,v_n$, with one red and one blue edge between each opposite
pair. A feasible solution is a perfect matching with an odd number of
red edges. Equivalently, it is a permutation $\sigma$ of $[n]$ together
with a Boolean color for each edge $(u_i,v_{\sigma(i)})$, with odd
total red count. This is the concrete Lean solution type `ParityMatching`.

Rows are Boolean labelings $a$ of the $2n$ vertices such that the number
of labels equal to one is congruent to $n$ modulo two. Call an edge a
violation if it is blue with equal endpoint labels or red with unequal
endpoint labels. Let $t_n(a,M)$ count the violations in $M$ and put

$$
P_{n,r}(a,M)=t_n(a,M)-r.
$$

The nonnegative-rank bound needed for this application is

$$
r_+(P_{n,r})=2^{\Omega_r(n)}
\quad\text{for fixed }0<r<1.
$$ (eq-lp-hardness-in-p-parity-source)

The mathematical proof of this separate shifted parity-matching assertion
is given in [](#thm-lp-hardness-in-p-parity-source). The original reduction
accepts this rank bound as a hypothesis. The additional Lean theorem
[](#cor-lp-hardness-in-p-jsy-lp) instead derives a finite lower bound
from explicit partition and probability-comparison hypotheses.
The argument extends the rectangle estimates of Jia, Svensson, and Yuan;
their exact bound at $r=1$ alone would not suffice, and the ordinary
matching bound of Braun and Pokutta concerns a different matrix.

```{prf:lemma} Parity-matching optimum
:label: lem-lp-hardness-in-p-parity-optimum

Let $n\ge1$ and $\gamma\ge0$. Give each edge cost one plus a penalty
$\gamma$ if it violates $a$. Every feasible matching has cost at least
$n+\gamma$, and some feasible matching attains this value.
```

```{prf:proof} of [](#lem-lp-hardness-in-p-parity-optimum)
:nonumber:

For a selected edge with red bit $b_i$, its violation bit is
$1+b_i+a(u_i)+a(v_{\sigma(i)})$ modulo two. Summing gives
$n+1+n=1$ modulo two, since $\sigma$ is a permutation.
Thus $t_n(a,M)$ is odd and at least one.

To attain one, choose the identity permutation, color every selected
edge so that it does not violate $a$, and reverse the color of one edge.
Before reversal the number of red edges is even; afterwards it is odd,
with exactly one violation. The selected-edge sum is
$n+\gamma t_n(a,M)$, proving the claim.
```

```{prf:theorem} LP lower bound for odd-red bipartite perfect matching
:label: thm-lp-hardness-in-p-parity

Fix $n\ge1$, $\alpha>1$, and $\gamma=2(\alpha-1)n$. Let
$L\le r_+(P_{n,1/(2\alpha)})$.
Every certified $\alpha$-approximate formulation for the above
odd-red bipartite perfect matching cost instances, with $m$
inequalities, satisfies $L\le m+1$.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-parity)
:nonumber:

The preceding optimum calculation gives the slack identity

$$
n+\gamma t_n(a,M)-\frac{n+\gamma}{\alpha}
=\gamma\left(t_n(a,M)-\frac1{2\alpha}\right).
$$

Use $\gamma>0$ and [](#thm-lp-hardness-in-p-factorization).
```

Applying [](#thm-lp-hardness-in-p-parity-source) gives
$2^{\Omega_\alpha(n)}$ inequalities for every fixed $\alpha>1$ on a
host with $2n$ vertices and $2n^2$ colored edges. All costs are positive
and at most $1+2(\alpha-1)n$. No metric restriction is asserted here.
The weighted odd-red problem is deterministically polynomial-time
solvable; see the discussion of weighted parity matching in
@jia2022exact, Section 1.
The condition is an odd red count, rather than an exactly prescribed
red count.

## The common reduction mechanism

The preceding arguments use simple scaling, restriction, and
transposition. The accompanying library also proves the more general
reduction used in
@braun2014affine
and @braun2015strong.

```{prf:theorem} Factorization reduction
:label: thm-lp-hardness-in-p-reduction

Suppose

$$
S(i,x)=A(i,x)\,T(f(i),g(x))+B(i,x).
$$

If $A,T,B$ have nonnegative factorizations with $a,k,b$ terms,
respectively, then $S$ has a nonnegative factorization with $ak+b$
terms. Zero terms are allowed.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-reduction)
:nonumber:

Pull back each row factor of $T$ along $f$ and each column factor along
$g$. Multiply these factors by every pair of factors in $A$, obtaining
$ak$ nonnegative rank-one terms. Append the $b$ factors of $B$.
```

```{prf:corollary} Transfer to formulation size
:label: cor-lp-hardness-in-p-general-transfer

Suppose $T$ is the slack of a certified target LP with $m$
inequalities, the preceding identity holds, and $A,B$ admit
factorizations with $a,b$ terms. If $L\le r_+(S)$, then
$L\le a(m+1)+b$.
```

```{prf:proof} of [](#cor-lp-hardness-in-p-general-transfer)
:nonumber:

Apply [](#thm-lp-hardness-in-p-factorization) followed by
[](#thm-lp-hardness-in-p-reduction).
```

The maps $f$ and $g$ are independent. Dependence on both indices may
occur in $A$ and $B$, and its nonnegative factorization size is
accounted for in the inequality.

```{prf:proposition} Transposition
:label: prop-lp-hardness-in-p-transpose

For every real matrix $S$, $r_+(S^{\mathsf T})=r_+(S)$.
```

```{prf:proposition} Positive row scaling
:label: prop-lp-hardness-in-p-scaling

If $c_i>0$ for all $i$, then
$r_+((c_iS(i,x))_{i,x})=r_+(S)$.
```

```{prf:proof} of [](#prop-lp-hardness-in-p-transpose) and [](#prop-lp-hardness-in-p-scaling)
:nonumber:

Transposition exchanges row and column factors. Row scaling multiplies
the row factors by $c_i$. Each operation has an inverse of the same
kind, so it preserves the possible factorization sizes, including
infinite rank.
```

### Bounded additive baselines

```{prf:corollary} Bounded-baseline transfer
:label: cor-lp-hardness-in-p-baseline

Let $\alpha>1$, $a_i>0$, and $b_i/a_i\le B$. Put
$r_0=(1-(\alpha-1)B)/\alpha$.
A certified formulation with values $a_iq(i,x)+b_i$ and bounds
$(a_i+b_i)/\alpha$ has $L\le m+2$ whenever
$L\le r_+(q-r_0)$.
```

```{prf:proof} of [](#cor-lp-hardness-in-p-baseline)
:nonumber:

The identity

$$
q(i,x)-r_0
=\frac{a_iq(i,x)+b_i-(a_i+b_i)/\alpha}{a_i}
 +\frac{\alpha-1}{\alpha}\left(B-\frac{b_i}{a_i}\right)
$$

expresses the source matrix as a positive row scaling of the target
slack plus a nonnegative row-constant matrix. The latter adds at most
one factor. To apply the matching source theorem with $0<r_0<1$,
one can additionally choose $0\le B<1/(\alpha-1)$.
```

### Objective reversal

The same contribution retains the near-exact objective-reversal
transfer. This auxiliary result is not needed for the four
fixed-factor applications above.

```{prf:corollary} Near-exact objective reversal
:label: cor-lp-hardness-in-p-reversal

Let $N>0$, let $v(i,x)$ be source values, and let $c(i,y)$ be target
costs. Suppose instance-independent maps $e:X\to Y$ and $h:Y\to X$
satisfy

$$
c(i,e(x))=N-v(i,x),\qquad c(i,e(h(y)))\le c(i,y).
$$

Let $o_i\ge0$ and $C_i-o_i\ge1/4$. A certified LP with values
$c(i,y)$ and bounds $(N-o_i)/(1+1/(4N))$ has $L\le m+2$
whenever $L\le r_+((C_i-v(i,x))_{i,x})$.
```

```{prf:proof} of [](#cor-lp-hardness-in-p-reversal)
:nonumber:

Pull the target slack back to $e(x)$ and add the row offset

$$
C_i-o_i-\frac{N-o_i}{4N+1}.
$$

This is nonnegative because $C_i-o_i\ge1/4$ and $o_i\ge0$.
The resulting matrix is $C_i-v(i,x)$, at a cost of at most one
additional factor.
```

Interpreting $o_i$ as the source maximum requires the corresponding
upper bound and an attaining solution. The library proves optimum
transfer from those additional hypotheses; the corollary does not
silently assume them.

## Source bound for the shifted parity matrix

This section proves the additional rank bound for odd-red bipartite
matching. **The new extension is formalized in Lean, conditional on
explicit assertions from the earlier partition framework.** These
assertions include the small- and bad-triple estimates, Equations
(4.5)–(4.6), and the permutation lemma, Lemma 4.4, of
@jia2022exact, Sections 4.2–4.6.
Their entropy proofs and the complete outside-partition construction are
not formalized here. The one-violation construction, its admissibility,
the new charging estimate, conversion to finite rank bounds, numerical
parameter choice, and padding are proved in Lean. The precise conditional
statements appear at the end of this section.

Write $L$ for a vertex labeling and $E_L$ for its violating edges; thus
$t(L,M)=t_n(L,M)=|M\cap E_L|$ and $P_{n,r}(L,M)=t(L,M)-r$.
Fix a sufficiently large integer $k$, let $h=4k+3$, and first take
$n=4k(2s+1)+3$, where $s$ tends to infinity. A partition consists of
ordered blocks $A_1,\ldots,A_s,B_1,\ldots,B_s$ of $4k$ vertex pairs
each, and an unordered core $C$ of $h$ pairs.
On an ordered block $D$, define $M_A(D)$ by the red edges
$(u_i,v_{2k+i})$ and $(u_{2k+i},v_i)$ for $1\le i\le2k$.
Let $L_B(D)$ assign one to both endpoints at positions
$1,\ldots,k,2k+1,\ldots,3k$, and zero at the other positions.
These matching and labeling choices have no violations.

Outside the core, fix $M_A$ on every $A$-block and choose any labeling
consistent with it; fix $L_B$ on every $B$-block and choose any matching
consistent with it. All such choices have the required even parities
outside $C$: consistency gives equal labels on each fixed red edge, and
the red-count parity of a consistent matching is the number of pairs
minus the number of labels equal to one.
For a fixed rectangle $\mathcal R=\mathcal L\times\mathcal M$,
write $p_M(J)$ and $p_L(K)$ for the respective probabilities of membership
in its factors when the core matching is $J$, or the core labeling is $K$,
and the permitted outside completions are sampled uniformly.
The two completions are independent.

```{prf:lemma} A finite rectangle inequality for parity matchings
:label: lem-lp-hardness-in-p-parity-corruption

For $0<\varepsilon<1/3$, sufficiently large $k$, and sufficiently large
$s$, there are probability distributions $\mu_3,\mu_h,\nu_1$ supported
on $t=3,h,1$, respectively, such that every rectangle satisfies
$$
\mu_3(\mathcal R)\le A\mu_h(\mathcal R)+B\nu_1(\mathcal R)+E_s,
$$
where
$$
p=\binom{2k+3}{3},\qquad
A=\frac{10k(1+\varepsilon)^2}{(1-\varepsilon)p},\qquad
B=\frac{3(1+\varepsilon)^6}{1-\varepsilon},\qquad
E_s=\frac{2^{-\delta s}+2^{-\zeta s}}{1-\varepsilon}.
$$
Here $\delta,\zeta>0$ depend only on $k,\varepsilon$.
```

```{prf:proof} of [](#lem-lp-hardness-in-p-parity-corruption)
:nonumber:

Sample the partition uniformly and order its core uniformly as
$C=F\sqcup D_2$, with $|F|=2k+3$ and $|D_2|=2k$.
Fix the family of bijections from JSY Lemma 4.4. For
$H\in\binom F3$, use the bijection indexed by the positions of $H$ in $F$
to order $F\setminus H$ as $D_{1,H}$, and put
$D_H=D_{1,H}\sqcup D_2$. The family has the following property:
in every family of at least $10k$ triples, there are $H,H'$ and
$i,j\in H'\setminus H$ lying in opposite halves of $D_{1,H}$.

Let $J_{3,H}$ be red identity edges on $H$ and $M_A(D_H)$ elsewhere.
Let $K_{3,H}$ assign $(1,0)$ to each pair in $H$ and equal $L_B(D_H)$
elsewhere. Their only violations are the three edges on $H$.
Set $g_H=p_M(J_{3,H})p_L(K_{3,H})$. Averaging over the partition,
the ordered core, and uniform $H$ defines $\mu_3(\mathcal R)$.
This is JSY's alternative sampling of their three-violation distribution:
conditional on $H$, the order of the remaining pairs is uniform,
regardless of the fixed bijection used to order $D_{1,H}$.

Let $J_h$ consist of all red identity edges on $C$.
Let $K_h$ label the pairs in $F$ by $(1,0)$ and those in $D_2$ by $(0,1)$.
Set $w=p_M(J_h)p_L(K_h)$. These completions do not depend on $H$,
have $h$ violations, and their average defines $\mu_h(\mathcal R)$.

Use JSY's good, small, and bad classification. Goodness means that, for
each factor separately, replacing its canonical completion on $D_H$
by any permitted completion changes its positive membership probability
by at most a factor $1+\varepsilon$. For the matching factor, permitted
means consistent with $L_B(D_H)$; for the labeling factor it means
consistent with $M_A(D_H)$. Both $J_h$ and $K_h$ are permitted replacements.
Consequently every good triple satisfies
$$
g_H\le(1+\varepsilon)^2w.
$$
The imported small- and bad-triple estimates are
$$
\mathrm{Small}\le2^{-\delta s},\qquad
\mathrm{Bad}\le\varepsilon\mu_3(\mathcal R)+2^{-\zeta s}.
$$
They hold for arbitrary rectangles: their proofs use slice densities,
entropy, and block exchanges, without excluding one-violation entries.
That exclusion is used in JSY's good-triple contradiction, which we now
replace by a quantitative estimate.

To make the use of the bad-triple estimate precise, on the labeling side
fix the labels on $H$ and all $B$-blocks. Let
$X=\prod_{i=0}^{s}X_i$ be the product of allowed labelings on $D=A_0$
and the $A$-blocks, and let $Y\subseteq X$ be the full set of completions
belonging to the rectangle's labeling factor. A nonsmall canonical
slice in coordinate $j$ gives
$|Y|/|X|\ge2^{-\delta s}/|X_j|$. The alphabet sizes depend only on $k$,
so this satisfies the entropy lemma's density hypothesis after adjusting
$\delta$. At an unbiased coordinate, every slice density lies within a
factor $1+\varepsilon/3$ of $|Y|/|X|$; any two therefore lie within a
factor $1+\varepsilon$. The block-exchange argument gives the stated
bad-triple bound, and the matching side is identical. Here $Y$ is the
full product-space subset, rather than a single fixed-coordinate slice.
No exclusion of one-violation entries is involved.

Define $\nu_1$ independently of the rectangle. Conditional on the partition
and ordered core, choose $H'\in\binom F3$ uniformly and then an unordered
pair $\{i,j\}\subset H'$ uniformly. Define $J'$ by red identity edges on
$C\setminus\{i,j\}$ and the two blue edges $(u_i,v_j),(u_j,v_i)$.
Define $K'$ to be one at every core vertex except the three right vertices
belonging to $H'$. The core has $h-2$ red edges and $2h-3$ labels equal
to one; both numbers are odd. Its only violation is the unchanged red
identity edge at the third element of $H'$. Complete outside as before.
This defines a probability distribution supported on $t=1$, using $3p$
equally weighted core indices.

Fix the partition and ordered core, and let $\mathcal G$ be the family of
good triples. Call $H'\in\mathcal G$ regular if some $H\in\mathcal G$
has $i,j\in H'\setminus H$ in opposite halves of $D_{1,H}$.
There are fewer than $10k$ exceptional triples: otherwise the permutation
lemma, applied to that exceptional subfamily, would produce a regular member.

For each regular $H'$, select one witness $H$ and pair $\{i,j\}$.
The corresponding $J'$ agrees with $J_{3,H}$ on $H$.
On $D_H$, its red identity edges are consistent with $L_B(D_H)$;
the two blue edges are also consistent because $i,j$ have opposite
$L_B(D_H)$ labels. Thus $J'$ is a permitted matching replacement for $H$.
The labeling $K'$ agrees with $K_{3,H'}$ on $H'$ and is identically one
on $D_{H'}$. Since $M_A(D_{H'})$ is entirely red, $K'$ is a permitted
labeling replacement for $H'$.
Comparison through the respective canonical completions gives
$$
p_M(J')\ge\frac{p_M(J_h)}{(1+\varepsilon)^2},
\qquad
p_L(K')\ge\frac{p_L(K_h)}{(1+\varepsilon)^2}.
$$
Different regular $H'$ give distinct indices $(H',\{i,j\})$ in the
sampling experiment defining $\nu_1$. Therefore
$$
\nu_1(\mathcal R\mid T,C)
\ge\frac{|\mathcal G_{\rm reg}|\,w}{3p(1+\varepsilon)^4}.
$$
Adding the at most $10k$ exceptional contributions yields
$$
\frac1p\sum_{H\in\mathcal G}g_H
\le\frac{10k(1+\varepsilon)^2}{p}w
  +3(1+\varepsilon)^6\nu_1(\mathcal R\mid T,C).
$$
Average this inequality, add the small- and bad-triple contributions,
and divide by $1-\varepsilon$.
```

```{prf:theorem} Rank of every fixed positive shift
:label: thm-lp-hardness-in-p-parity-source

For every fixed $0<r\le1$, the parity matrix satisfies
$$
r_+(P_{n,r})=2^{\Omega_r(n)}.
$$
```

```{prf:proof} of [](#thm-lp-hardness-in-p-parity-source)
:nonumber:

Set $W=\mu_3-A\mu_h-B\nu_1$. Its value on each rectangle indicator is at
most $E_s$. On the matrix $P_{n,r}=t-r$, its value is
$$
\langle W,P_{n,r}\rangle
=(3-r)-A(h-r)-B(1-r)
=2r-A(h-r)-(B-3)(1-r).
$$
Choose $\varepsilon=r/100$ and $k\ge400/r$, also sufficiently large
for the permutation lemma. The formal parameter estimates give
$A(4k+3)\le r/10$ and $B-3\le r/4$; hence the displayed value is
greater than $3r/2$.

For completeness, if a finite signed matrix $W$ has value at most $E$
on every rectangle indicator, then any nonnegative matrix $S$ satisfies
$$
r_+(S)\ge\frac{\langle W,S\rangle}{E\|S\|_\infty}
$$
whenever the numerator and $E$ are positive. Normalize a nonzero
nonnegative rank-one summand $ab^{\mathsf T}$ by the maxima of its two
factors. The resulting factors lie in unit cubes. Maximizing a linear
functional in each factor in turn shows that their signed pairing is
at most the largest rectangle weight. The original summand therefore
contributes at most $E\|a\|_\infty\|b\|_\infty$. Since each summand of a
nonnegative factorization is entrywise at most $S$, this is at most
$E\|S\|_\infty$. Summing proves the inequality. This finite argument,
including empty index sets and zero factors, is formalized in Lean.

Here $0\le P_{n,r}\le n$, while $E_s$ is exponentially small in $s$ and
$s=\Theta_r(n)$. This proves the lower bound for
$n=4k(2s+1)+3$. For arbitrary sufficiently large $n$, take the largest
such $n_0\le n$ and add blue identity matching edges with endpoint labels
$(1,0)$. They add no violations, preserve odd red parity, and change the
label parity by precisely $n-n_0$. Thus $P_{n_0,r}$ occurs as a submatrix
of $P_{n,r}$, with $n-n_0<8k$. The bound follows for all sufficiently
large $n$.
```

### Formal statements for the extension

The finite statements below specify exactly which part of the preceding
argument Lean proves. They use the same costs and violation matrices as
the four applications.

```{prf:proposition} The new one-violation distribution
:label: prop-lp-hardness-in-p-core-distribution

Let $h$ be odd. Take any finite probability distribution on samples
$(H',i,j)$ with $H'\subseteq[h]$, $|H'|=3$, and distinct $i,j\in H'$.
Apply the core matching and labeling construction above to each sample.
Its distribution on actual admissible labelings and odd-red matchings
is supported on pairs with exactly one violation.
```

```{prf:proof} of [](#prop-lp-hardness-in-p-core-distribution)
:nonumber:

The matching has $h-2$ red edges and the labeling has $2h-3$ labels
equal to one. The two swapped blue edges do not violate, and precisely
the third element of $H'$ contributes a violating red edge. Pushing
forward the sample weights preserves total mass and this support
property, including when several samples give the same outcome.
```

For clarity, call the following the *finite partition hypotheses*.
There is a finite set of partitions with nonnegative averaging weights
and a finite set of $p$ triples. Each partition specifies its good triples,
canonical and high-violation completions, and nonnegative row and column
membership probabilities. The following assertions are supplied:

- Every family of at least $K$ good triples contains the witness pair
  guaranteed by the permutation-family property.
- For a good triple, the probability of every permitted completion is
  within a factor $c=1+\varepsilon$ of its canonical probability.
  Permitted matchings agree with the red identity matching on that
  triple and are consistent with the complementary labeling.
  Permitted labelings have the canonical values on the triple and
  are consistent with the complementary matching.
- The high completions are permitted. The old canonical matchings
  and labelings have the block properties described above; the
  witness relation gives two opposite labels outside the witness triple.
- The averages of the high-completion probabilities and the new
  one-violation sample probabilities equal the respective rectangle
  masses. The three-violation mass is covered by the good, small,
  and bad contributions, with
  $\mathrm{Small}\le e_s$ and
  $\mathrm{Bad}\le\varepsilon\mu_3(\mathcal R)+e_b$.

These are explicit fields of `ConcreteJSYRectangleData`. Its new matching
and labeling are the concrete core constructions, not arbitrary
replacement objects. Lean proves that they are permitted and derives
their probability comparisons from the generic goodness condition.
The sampling identities, permutation-family assertion, and small-/bad-triple
estimates remain hypotheses; their proofs in the earlier framework are
outside this formalization.

```{prf:theorem} Finite corruption inequality from the partition hypotheses
:label: thm-lp-hardness-in-p-formal-corruption

Assume the finite partition hypotheses, $p>0$, and
$0\le\varepsilon<1$. Then

$$
\mu_3(\mathcal R)\le
\frac{K(1+\varepsilon)^2}{(1-\varepsilon)p}\,\mu_h(\mathcal R)
+\frac{3(1+\varepsilon)^6}{1-\varepsilon}\,\nu_1(\mathcal R)
+\frac{e_s+e_b}{1-\varepsilon}.
$$

Neither this corruption inequality nor a rank lower bound is a hypothesis.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-formal-corruption)
:nonumber:

Apply the permutation property to the exceptional family itself to
bound its size by $K$. For every regular triple, the new permitted
matching and labeling have product probability at least $w/c^4$,
whereas its canonical product is at most $c^2w$. Its contribution is
therefore at most $c^6$ times the sum of its three new sample
probabilities. Sum over triples, divide by $p$, average over
partitions, and absorb the bad contribution
$\varepsilon\mu_3(\mathcal R)$. This proves the displayed coefficients.
```

```{prf:theorem} Separation from rectangle bounds
:label: thm-lp-hardness-in-p-separation

Let $S,W$ be real matrices on finite index sets. Suppose every rectangle
has signed $W$-weight at most $E\ge0$ and $S(i,j)\le U$ for all entries,
where $U\ge0$. Every nonnegative factorization of $S$ with $q$ terms
satisfies

$$
\langle W,S\rangle\le qEU.
$$
```

```{prf:proof} of [](#thm-lp-hardness-in-p-separation)
:nonumber:

Apply the finite unit-cube argument from the preceding proof to each
rank-one summand. Its entries are bounded above by those of $S$, so
each summand contributes at most $EU$.
```

```{prf:proposition} Explicit parameter choice
:label: prop-lp-hardness-in-p-parameters

Let $0<r\le1$, $\varepsilon=r/100$, and $k\in\mathbb N$ satisfy
$k\ge400/r$. With $A,B$ defined in the finite rectangle inequality,

$$
(3-r)-A(4k+3-r)-B(1-r)>\frac{3r}{2}.
$$
```

```{prf:proof} of [](#prop-lp-hardness-in-p-parameters)
:nonumber:

The exact identity
$6\binom{2k+3}{3}=(2k+3)(2k+2)(2k+1)$ gives $A\le8/k^2$.
Also $(1+\varepsilon)^6\le1+7\varepsilon$ for
$0\le\varepsilon\le1/100$, giving $B-3\le25\varepsilon$.
Consequently $A(4k+3)\le r/10$ and $B-3\le r/4$.
Substitute these bounds into
$2r-A(4k+3-r)-(B-3)(1-r)$.
```

```{prf:theorem} Finite shifted-rank bound
:label: thm-lp-hardness-in-p-finite-extension

Let $\mu_3,\mu_h,\nu_1$ be probability matrices supported on
$t=3,h,1$, respectively, where $h=4k+3$. Assume the finite partition
hypotheses for every rectangle, with
$K=10k$, $p=\binom{2k+3}{3}$, $\varepsilon=r/100$,
$0<r\le1$, and $k\ge400/r$. Suppose $e_s,e_b\ge0$ and
$t(i,j)-r\le U$, where $U\ge0$. Set
$E=(e_s+e_b)/(1-r/100)$.
For every $L\in\mathbb N$,

$$
(L-1)EU\le\frac{3r}{2}
\quad\Longrightarrow\quad
L\le r_+(t-r).
$$

Here $L-1$ is subtraction in the real numbers.
```

```{prf:proof} of [](#thm-lp-hardness-in-p-finite-extension)
:nonumber:

The corruption theorem bounds every rectangle of
$W=\mu_3-A\mu_h-B\nu_1$ by $E$. Support and normalization give
$\langle W,t-r\rangle=(3-r)-A(h-r)-B(1-r)>3r/2$.
A factorization with fewer than $L$ terms would contradict
[](#thm-lp-hardness-in-p-separation).
```

```{prf:corollary} Parity-matching LP bound from the partition hypotheses
:label: cor-lp-hardness-in-p-jsy-lp

In the preceding theorem take the actual parity violation matrix $t_n$,
$r=1/(2\alpha)$, $\alpha>1$, and $U=n\ge1$.
Assume the concrete finite partition hypotheses.
Every certified $\alpha$-approximate formulation for the positive-cost
odd-red matching family has $L\le m+1$ whenever
$(L-1)En\le3r/2$.
```

```{prf:proof} of [](#cor-lp-hardness-in-p-jsy-lp)
:nonumber:

Every matching has at most $n$ violations, so $t_n-r\le n$.
Derive the shifted rank bound from the partition hypotheses and apply
[](#thm-lp-hardness-in-p-parity). The formal endpoint performs both
steps; it does not assume a source rank bound.
```

```{prf:proposition} Padding the parity matrix
:label: prop-lp-hardness-in-p-padding

For $n\le N$ and every real $r$,
$r_+(P_{n,r})\le r_+(P_{N,r})$.
```

```{prf:proof} of [](#prop-lp-hardness-in-p-padding)
:nonumber:

Add blue identity edges and label the new endpoint pairs $(1,0)$.
These independent maps preserve both parity conditions and the exact
violation count. The smaller matrix is a pullback of the larger one.
```

## Scope of the formalization

The four final Lean theorems use actual combinatorial solutions.
Perfect matchings are finite simple graphs of degree one, $V$-joins
are finite simple graphs with all degrees odd, odd cuts are odd
finite vertex subsets, and colored bipartite matchings are permutations
with edge colors. Edge counts and objective sums are defined on these
objects.

The formal proofs include the one-crossing matching construction,
degree-sum arguments, the singleton odd-cut optimum, the parity
identity and one-violation matching construction, all four exact
optimum calculations, and the transfers to $L\le m+1$.
The metric property is proved for the actual cost function.
The first three applications use a graph with $n$ vertices; the
parity application uses a multigraph with $2n$ vertices.

The remaining external hypotheses and results are:

- the ordinary matching-matrix nonnegative-rank theorem of Braun and Pokutta;
- for the new parity extension, the permutation-family property, generic
  good-completion comparisons, sampling identities, and small-/bad-triple
  estimates of the Jia–Svensson–Yuan framework; the full-graph completion
  maps are required to preserve the core violation count;
- the existence of affine Farkas certificates, provided as data in
  `CertifiedLP`;
- the cited polynomial-time algorithms, whose running times are not
  formalized here.

The original four transfer theorems remain available with an assumed
source rank bound. The additional parity theorem instead derives that
rank bound, in finite quantitative form, from the displayed partition
hypotheses. The mathematical exponential statement also uses the
exponential decay in the external small-/bad-triple estimates.
The Lean development does not formalize the earlier paper in its entirety.

All four applications can be imported from one module:

```{literalinclude} ../../lean/Lemmata/LPHardnessInP/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/lp-hardness-in-p.md
```
