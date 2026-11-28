---
title: "Oracle complexity of nonsmooth convex optimization via information theory"
numbering:
  headings: false
---

```{include} ../_generated/provenance/nonsmooth-oracle-complexity.md
```

:::{note}
This entry formalizes results of the paper *Lower Bounds on the Oracle Complexity of Nonsmooth
Convex Optimization via Information Theory* by Gábor Braun, Cristóbal Guzmán and Sebastian Pokutta
[@braun2017lower], currently the information-theoretic lower bound and the string guessing problem
in expectation and in probability (Lemma III.1, Proposition III.3), oracle emulation (Lemma III.5),
the lower bounds for nonsmooth convex optimization over the box (Section IV) and over $\ell^p$-balls
(Section V) with local single-coordinate oracles, and the maximal oracle (Lemma VI.2); numbers refer
to the arXiv version.
:::

How many oracle queries does an algorithm need to minimize a nonsmooth convex function? The paper
answers this with information theory instead of the resisting oracles of Nemirovski and Yudin: an
unknown instance carries a certain amount of entropy, every oracle answer reveals only a bounded
amount of information about it, so many answers are needed to identify it. This bounds the
distributional complexity of algorithms that may err with some probability, and through emulations
it transfers from one oracle to another.

## Query algorithms and information

A deterministic adaptive algorithm is a query tree: it either stops with an output, or asks a query
and continues with the subtree for the answer it receives. The instance $f$ is drawn from a finite
set $F$ with probabilities $p$, and the oracle answers query $q$ by $O_f(q)$. The algorithm asks
$T(f)$ queries and outputs a guess of the instance, wrong with probability $P_e$.

```{prf:definition} Information per query
:label: def-nonsmooth-oracle-complexity-information
:nonumber:

A query tree reveals at most $C$ nats per query if at every query $q$, with $G$ the set of instances
for which the algorithm asks $q$, the answer $O_f(q)$ has conditional entropy at most $C$ given
$f \in G$.
```

The answers are determined by the instance, so this conditional entropy is the information
$I[F; A_t \mid \Pi_{\lt t}, Q_t, T \ge t]$ of the paper.

```{prf:lemma} Information-theoretic lower bound
:label: lem-nonsmooth-oracle-complexity-information
:enumerator: III.1

If a query tree reveals at most $C$ nats per query and identifies the instance with error
probability $P_e$, then

$$
H(F) \le C\, \mathbb{E}[T] + h(P_e) + P_e \log(|F| - 1),
$$

so $\mathbb{E}[T] \ge (H(F) - h(P_e) - P_e \log(|F| - 1))/C$ for $C > 0$, where $h$ is the binary
entropy.
```

All entropies are kept multiplied by the probability of the event they condition on, so no division
occurs. By the chain rule, the entropy of the instance given the instances reaching a query splits
into the entropy of the answer, at most $C$ times their probability, and the entropies given the
answers. Unfolding the tree, $H(F)$ is at most $C\, \mathbb{E}[T]$ plus the entropy left at the
leaves. At a leaf with output $o$, Fano's inequality bounds the entropy left by the binary entropy
of the error plus the error times $\log(|F| - 1)$, in scaled form. The scaled binary entropy
$P h(e/P)$ is superadditive because $h$ is concave, so the leaves add up to
$h(P_e) + P_e \log(|F| - 1)$.

:::{admonition} Errata
:class: warning
The second claim of Lemma III.1, $\mathbb{P}[T \lt t] \le (h(P_e) + P_e \log |F| + C t)/H(F)$, fails
for non-uniform priors. Let $F = \{0, 1, \dots, 1024\}$ with $p_0 = 1/2$ and $p_i = 1/2048$
otherwise, so that $H(F) = 6$ bits. An algorithm first asks whether $f = 0$, and otherwise learns
the index bit by bit; every answer reveals one bit, and $P_e = 0$. Then $\mathbb{P}[T \lt 2] = 1/2$,
while the bound gives $2/6$. The proof bounds the information $I[F; \Pi \mid \Pi_{\le t}, T \ge t]$
by $H(F)$, but given the event $T \ge t$ the entropy of the instance can exceed $H(F)$; it is at
most $\log |F|$. This gives the corrected bound below, with the extra term $\log |F| - H(F)$. For
the uniform prior, which is how the paper uses the claim, this term vanishes and the bound is the
paper's.
:::

```{prf:lemma} Information-theoretic lower bound in probability (corrected)
:label: lem-nonsmooth-oracle-complexity-information-tail
:enumerator: III.1

Under the hypotheses of Lemma III.1 with $C \ge 0$ and $P_e \le 1/2$, for every $d$

$$
\mathbb{P}[T \lt d] \log |F| \le \log |F| - H(F) + C d + h(P_e) + P_e \log(|F| - 1).
$$
```

Run the chain rule for $d$ steps only: $H(F)$ is at most $C\, \mathbb{E}[\min(T, d)] \le C d$ plus
the entropy left at the leaves reached before depth $d$ and at the nodes of depth $d$. Fano's
inequality bounds the former by $h(E) + E \log(|F| - 1)$, where $E \le P_e$ is the probability of an
error before depth $d$. The entropy left at a node of depth $d$ is at most its probability times
$\log |F|$, and these add up to $\mathbb{P}[T \ge d] \log |F|$.

## The string guessing problem

The source of hardness is a hidden binary string $S \in \{0, 1\}^M$, drawn uniformly at random. Its
oracle accepts guesses of any of the bits and reveals only how far the guesses were right.

```{prf:definition} String guessing oracle (Oracle III.2)
:label: def-nonsmooth-oracle-complexity-string-oracle
:nonumber:

A query is a list of guesses $(i_1, b_1), \dots, (i_k, b_k)$ of bits $S_{i_j} = b_j$. The answer is
the index of the first wrong guess, or that all guesses are right.
```

```{prf:proposition} String guessing problem
:label: prop-nonsmooth-oracle-complexity-string-guessing
:enumerator: III.3

Every deterministic algorithm that identifies a uniformly random string $S \in \{0, 1\}^M$ with the
string guessing oracle and error probability $P_e$ asks at least
$((1 - P_e) M - h(P_e)/\log 2)/2 \ge ((1 - P_e) M - 1)/2$ queries in expectation.
```

The oracle reveals nothing about the bits after the first wrong guess. Hence the strings that reach
a query form a cylinder: they agree with a partial assignment of the bits. On a cylinder the answer
has entropy at most $2 \log 2$. A guess of a bit that the cylinder fixes either ends the answer or
is skipped; a guess of a free bit splits the cylinder into two halves, the answer at this guess on
one half and a later answer on the other, at the cost of one bit plus half the entropy of the rest.
Lemma III.1 with $H(S) = M \log 2$, $C = 2 \log 2$ and $\log(2^M - 1) \le M \log 2$ gives the bound.

```{prf:proposition} String guessing in probability
:label: prop-nonsmooth-oracle-complexity-string-tail
:enumerator: III.3

For every $d$, such an algorithm stops after fewer than $d$ queries with probability at most
$P_e + (2d + 1)/M$. So $T \ge c M$ holds with probability at least $1 - P_e - 2c - 1/M$, which makes
the paper's $\mathbb{P}[T = \Omega(M)] = 1 - P_e - o(1)$ precise.
```

This is the corrected Lemma III.1 for the uniform prior, with $C = 2 \log 2$; bounding $h$ by
$\log 2$ removes the condition $P_e \le 1/2$.

```{prf:lemma} Oracle emulation
:label: lem-nonsmooth-oracle-complexity-emulation
:enumerator: III.5

If the oracle $O_1$ is emulated by the oracle $O_2$, with a query translation $q$ and an answer
translation $a$ such that $O_1(x) = a(x, O_2(q(x)))$ on every instance, then every query algorithm
for $O_1$ turns into one for $O_2$ with the same output and the same number of queries on every
instance.
```

The new algorithm asks $q(x)$ whenever the old one asks $x$ and continues with the old subtree for
the translated answer. So lower bounds for $O_2$ hold for $O_1$: the paper emulates convex
optimization oracles by a string guessing oracle and transfers its lower bound.

## Nonsmooth convex optimization in one dimension

The hard instances encode a binary string in nested intervals. The interval of the first $j$ bits of
$S \in \{0, 1\}^M$ has center $c_j(S) = \sum_{i \lt j} \pm 4^{-(i+1)}$, the sign given by bit $i$,
and radius $4^{-j}$; every bit selects the left or the right part of the current interval.

```{prf:definition} Hard functions
:label: def-nonsmooth-oracle-complexity-box-fn
:nonumber:

For $S \in \{0, 1\}^M$, the hard function is
$f_S(x) = \max_{0 \le j \le M} \bigl(b_j - 8^{-j} + 2^{-j} |x - c_j(S)|\bigr)$ with the levels
$b_j = 1 - \frac{4}{7}(1 - 8^{-j})$. The piece of depth $j$ equals $b_j$ at the endpoints of the
interval of depth $j$.
```

This is the paper's recursive construction: each new bit replaces the function on part of the
current interval by a flatter absolute value centered in the new interval.

```{prf:definition} Oracle
:label: def-nonsmooth-oracle-complexity-box-oracle
:nonumber:

The oracle answers the query $x$ with the value $f_S(x)$ and the right derivative of $f_S$ at $x$ if
it is positive, otherwise the left derivative. The one-sided derivatives are the largest right slope
and the smallest left slope of the pieces that attain the maximum at $x$.
```

```{prf:proposition} The hard functions and their oracle
:label: prop-nonsmooth-oracle-complexity-box-valid
:nonumber:

The hard functions are convex and $1$-Lipschitz, and the oracle answers their value and a
subgradient.
```

```{prf:lemma} Packing
:label: lem-nonsmooth-oracle-complexity-packing
:enumerator: IV.3

The minimum of $f_S$ is $b_M - 8^{-M}$, attained at $c_M(S)$. For $\varepsilon \lt 8^{-M}$, a point
that is $\varepsilon$-optimal for $f_S$ and for $f_{S'}$ has $S = S'$.
```

At an $\varepsilon$-optimal point the piece of depth $M$ is below $b_M$, so the point lies within
$4^{-M}$ of $c_M(S)$. There the greedy path, which moves from the current center a quarter of the
radius towards the point, follows the bits of $S$; so the point determines $S$.

:::{admonition} Errata
:class: warning
Lemma IV.3 claims the packing property for $M = \lfloor \frac13 \log_2(1/\varepsilon) \rfloor$,
which allows $\varepsilon = 8^{-M}$. Then it fails: for $\varepsilon = 1/8$ and $M = 1$ the point
$0$ is the common endpoint of the intervals of the strings $0$ and $1$, and $f_0(0) = f_1(0) = 1/2$
exceeds the minimum $3/8$ of both functions by exactly $\varepsilon$. The proof needs
$\varepsilon \lt 8^{-M}$, as stated here. Lemma IV.6 inherits the same boundary case.
:::

```{prf:lemma} Emulation by string guessing
:label: lem-nonsmooth-oracle-complexity-box-emulation
:enumerator: IV.5

The oracle of the hard functions is emulated by the string guessing oracle on strings of length $M$.
```

The query asks for the bits of the greedy path towards $x$, and the answer reveals the first bit $k$
where $S$ leaves it. Then $x$ lies outside the interval of the first $k + 1$ bits of $S$, where
every deeper piece lies below the piece of depth $k + 1$. A deeper piece can reach the maximum only
if $S$ leaves the path to the right of $x$; then its slopes at $x$ are negative and no steeper than
those of the piece of depth $k + 1$, so it changes neither the left derivative nor a positive right
derivative. The answer therefore depends only on the first $k + 1$ bits of $S$, which the query
reveals.

An oracle is *local* if instances that agree near $x$ get the same answer at $x$; a non-local
first-order oracle could choose its subgradient at a kink to encode the minimizer.

```{prf:definition} Local oracle
:label: def-nonsmooth-oracle-complexity-local
:nonumber:

An oracle $O$ for a family of functions $f_s$ is local if $O_s(x) = O_{s'}(x)$ whenever $f_s$ and
$f_{s'}$ agree on a neighborhood of $x$.
```

```{prf:lemma} Locality
:label: lem-nonsmooth-oracle-complexity-box-local
:enumerator: IV.5

The oracle of the hard functions of Section IV.A is local.
```

Every piece is affine on each side of $x$ near $x$, and the pieces below the maximum stay below it
nearby, so $f_S$ is affine on each side of $x$ near $x$ with its one-sided derivatives as slopes.
Functions that agree near $x$ therefore have the same one-sided derivatives at $x$.

```{prf:theorem} Lower bound in one dimension
:label: thm-nonsmooth-oracle-complexity-box
:enumerator: IV.2

Let $S \in \{0, 1\}^M$ be uniformly random and $\varepsilon \lt 8^{-M}$. Every deterministic
algorithm that queries the oracle of $f_S$ and outputs an $\varepsilon$-minimizer with error
probability $P_e$ asks at least $((1 - P_e) M - 1)/2$ queries in expectation; with
$M \approx \frac13 \log_2(1/\varepsilon)$ this is $\Omega((1 - P_e) \log(1/\varepsilon))$.
```

By Lemmas IV.5 and III.5 the algorithm runs with the string guessing oracle, with the same number of
queries, and by Lemma IV.3 the greedy path of its output recovers $S$ whenever the output is
$\varepsilon$-optimal. Proposition III.3 then bounds the number of queries.

## Nonsmooth convex optimization over the box

In $n$ dimensions the instances are $n$-tuples of strings, one for each coordinate.

```{prf:definition} Hard functions of Section IV.B
:label: def-nonsmooth-oracle-complexity-cube-fn
:nonumber:

For $S = (S_1, \dots, S_n)$ with $S_i \in \{0, 1\}^M$, the hard function is
$f_S(x) = \max_i f_{S_i}(x_i)$, with the one-dimensional hard functions $f_{S_i}$.
```

```{prf:definition} Single-coordinate oracle
:label: def-nonsmooth-oracle-complexity-cube-oracle
:nonumber:

The oracle answers the query $x$ with the value $f_S(x)$, the least coordinate $i$ with
$f_{S_i}(x_i) = f_S(x)$, and the slope $\lambda$ of the one-dimensional oracle of $f_{S_i}$ at
$x_i$; the subgradient is $\lambda e_i$.
```

```{prf:proposition} The hard functions and their oracle
:label: prop-nonsmooth-oracle-complexity-cube-valid
:nonumber:

The hard functions are convex and $1$-Lipschitz for the maximum norm, and the oracle answers their
value and a subgradient that lies on a coordinate axis.
```

```{prf:lemma} Packing
:label: lem-nonsmooth-oracle-complexity-cube-packing
:enumerator: IV.6

The minimum of $f_S$ is $b_M - 8^{-M}$, attained at the point with coordinates $c_M(S_i)$, and for
$\varepsilon \lt 8^{-M}$ a point that is $\varepsilon$-optimal for $f_S$ and for $f_{S'}$ has
$S = S'$.
```

All one-dimensional hard functions have the same minimum, so every coordinate of an
$\varepsilon$-minimizer is $\varepsilon$-minimal for its own function and decodes its string.

```{prf:lemma} Emulation by string guessing
:label: lem-nonsmooth-oracle-complexity-cube-emulation
:enumerator: IV.7

The oracle of Section IV.B is emulated by the string guessing oracle on the concatenation of
$S_1, \dots, S_n$, a string of length $n M$.
```

A label $(i, k)$ stands for bit $k$ of coordinate $i$; its value is the value of coordinate $i$ if
$S_i$ first leaves the greedy path towards $x_i$ at bit $k$. These values decrease in $k$. The query
guesses the bits of all greedy paths in the confidence order: larger values first, then smaller
coordinates, then smaller bits. If the first wrong guess is at the label $(i, k)$, then $S_i$ leaves
its path at bit $k$, and every other coordinate either follows its path throughout or has value at
most that of its first label after $(i, k)$, which comes later in the order. So the value, the least
coordinate attaining it and its slope are determined by the answer.

```{prf:lemma} Locality
:label: lem-nonsmooth-oracle-complexity-cube-local
:enumerator: IV.7

The oracle of Section IV.B is local.
```

Moving one coordinate changes $f_S$ only through that coordinate. A coordinate that attains the
maximum raises $f_S$ when moved in the direction of its oracle slope, at that rate, and the other
coordinates leave $f_S$ unchanged nearby; so the function near $x$ determines the answer.

```{prf:theorem} Lower bound over the box
:label: thm-nonsmooth-oracle-complexity-cube
:enumerator: IV.2

Let $S_1, \dots, S_n \in \{0, 1\}^M$ be uniformly random and $\varepsilon \lt 8^{-M}$. Every
deterministic algorithm that queries the single-coordinate oracle of $f_S$ and outputs an
$\varepsilon$-minimizer with error probability $P_e$ asks at least $((1 - P_e) n M - 1)/2$ queries
in expectation, that is $\Omega((1 - P_e) n \log(1/\varepsilon))$.
```

Concatenation is a bijection between $n$-tuples of strings of length $M$ and strings of length
$n M$, so Proposition III.3 for strings of length $n M$ applies as in one dimension.

## Lower bounds over $\ell^p$-balls

Over the unit ball $B_p$ of the $\ell^p$ norm, $1 \le p \lt \infty$, the complexity need not grow
with the dimension when $\varepsilon$ is large. The instances are signs $s \in \{\pm 1\}^M$ on
$M \le n$ coordinates.

```{prf:definition} Hard functions of Section V.A
:label: def-nonsmooth-oracle-complexity-lp-fn
:nonumber:

For $s \in \{\pm 1\}^M$ and $M \le n$, the hard function is $f_s(x) = \max_{i \le M} s_i x_i$ on
$\mathbb{R}^n$, minimized over $B_p$.
```

```{prf:definition} Single-coordinate oracle of Section V.A
:label: def-nonsmooth-oracle-complexity-lp-oracle
:nonumber:

The oracle answers the query $x$ with the value $f_s(x)$, the least $i$ with $s_i x_i = f_s(x)$, and
the sign $s_i$; the subgradient is $s_i e_i$.
```

```{prf:proposition} The hard functions and their oracle
:label: prop-nonsmooth-oracle-complexity-lp-valid
:nonumber:

For $p \ge 1$, the hard functions are convex and $1$-Lipschitz for the $\ell^p$ norm, and the oracle
answers their value and a subgradient on a coordinate axis.
```

```{prf:lemma} Packing
:label: lem-nonsmooth-oracle-complexity-lp-packing
:enumerator: V.3

Let $p \ge 1$ and $M \varepsilon^p \lt 1$. A point of $B_p$ that is $\varepsilon$-optimal over $B_p$
for $f_s$ and for $f_{s'}$ has $s = s'$.
```

The point $x^\star = -M^{-1/p} (s_1, \dots, s_M, 0, \dots, 0)$ lies on the unit sphere of $\ell^p$,
and $f_s(x^\star) = -M^{-1/p} \lt -\varepsilon$. So an $\varepsilon$-minimizer $x$ over $B_p$ has
$s_i x_i \le f_s(x) \lt 0$ for all $i$, and the signs of $x$ recover $s$.

:::{admonition} Errata
:class: warning
For $1 \le p \lt 2$ the paper aims at the larger bound $\Omega(1/\varepsilon^2)$. It works in the
orthonormal basis $\xi_i = \nu_i / \sqrt{M}$, where the $\nu_i$ are the rows of the
Sylvester–Hadamard matrix $H$ of size $M = 2^l \lt \varepsilon^{-2}$, and compares with the point
with coordinates $-s_i / \sqrt{M}$ in this basis. It claims that this point lies in $B_p$ because
$\|x\|_p \le \|x\|_2$ for $p \lt 2$, but the inequality goes the other way, and Lemma V.3 fails.
Averaging the terms of $f_s(x) = \max_i s_i \langle \xi_i, x \rangle$ gives
$f_s(x) \ge -\|H s\|_\infty / (M \sqrt{M})$ on $B_1$. For $p = 1$, $\varepsilon = 1/4$, $M = n = 8$
and $s = (1, 1, 1, 1, 1, 1, -1, -1)$, $\|H s\|_\infty = 4$, so
$f_s \ge -1/(2 \sqrt{8}) \approx -0.177$ on $B_1$ (with equality at the minimum, by linear
programming), and the same holds for $-s$. The origin is then $\varepsilon$-optimal for both $f_s$
and $f_{-s}$. The standard basis, used here for all $p$, gives the bound $\Omega(1/\varepsilon^p)$.
This is the paper's bound for $p \ge 2$ and weaker for $p \lt 2$.
:::

```{prf:lemma} Emulation by string guessing
:label: lem-nonsmooth-oracle-complexity-lp-emulation
:enumerator: V.4

The oracle of Section V.A is emulated by the string guessing oracle on $s$, a string of length $M$.
```

The query guesses, in the order of decreasing $|x_i|$ and then increasing $i$, the signs
$s_i = -\operatorname{sign} x_i$, and $s_i = +1$ if $x_i = 0$, which make every term
$s_i x_i = -|x_i|$. If the first wrong guess is at $j$, then $s_j x_j = |x_j|$, the earlier terms
are $-|x_i| \le 0$, and the later ones are at most $|x_i| \le |x_j|$, with equality only at larger
indices. So $f_s(x) = |x_j|$, and the least coordinate attaining it and its sign are determined by
the answer. If all guesses are right, the answer determines $s$.

```{prf:lemma} Locality
:label: lem-nonsmooth-oracle-complexity-lp-local
:enumerator: V.4

The oracle of Section V.A is local.
```

A coordinate $i$ with $s_i x_i = f_s(x)$ raises $f_s$ at rate $1$ when moved in the direction $s_i$
and does not raise it in the opposite direction; any other coordinate leaves $f_s$ unchanged nearby.
So the function near $x$ determines the answer.

```{prf:theorem} Large-scale lower bound over $\ell^p$-balls
:label: thm-nonsmooth-oracle-complexity-lp
:enumerator: V.1

Let $p \ge 1$, $M \le n$ and $M \varepsilon^p \lt 1$, and let $s \in \{\pm 1\}^M$ be uniformly
random. Every deterministic algorithm that queries the single-coordinate oracle of $f_s$ and outputs
an $\varepsilon$-minimizer of $f_s$ over $B_p$ with error probability $P_e$ asks at least
$((1 - P_e) M - 1)/2$ queries in expectation. For $\varepsilon \ge n^{-1/p}$ and
$M = \lfloor \varepsilon^{-p} \rfloor - 1$ this is $\Omega((1 - P_e)/\varepsilon^p)$, independently
of the dimension.
```

As in Section IV: the signs of the output decode $s$, Lemma V.4 emulates the oracle, and Proposition
III.3 applies to strings of length $M$.

For small $\varepsilon$ the box bound takes over. The cube $[-\rho, \rho]^n$ with $\rho = n^{-1/p}$
lies in $B_p$.

```{prf:definition} Rescaled hard functions
:label: def-nonsmooth-oracle-complexity-scaled-fn
:nonumber:

The hard functions of Section IV.B rescaled into the cube are $g_S(x) = \rho f_S(x/\rho)$. Their
oracle answers $\rho$ times the value and the subgradient of the single-coordinate oracle of $f_S$
at $x/\rho$.
```

```{prf:proposition} Low-scale lower bound over $\ell^p$-balls
:label: prop-nonsmooth-oracle-complexity-low-scale
:enumerator: V.5

Let $p \ge 1$ and $\varepsilon \lt n^{-1/p} 8^{-M}$. The rescaled hard functions are convex and
$1$-Lipschitz for the $\ell^p$ norm, their oracle answers the value and a subgradient on a
coordinate axis, and they attain their minimum in $B_p$. Every deterministic algorithm that queries
the rescaled oracle and outputs an $\varepsilon$-minimizer of $g_S$ over $B_p$ with error
probability $P_e$ asks at least $((1 - P_e) n M - 1)/2$ queries in expectation. For
$\varepsilon \le n^{-1/p - \delta}$ with $\delta \gt 0$ this is
$\Omega((1 - P_e) n \log(1/\varepsilon))$.
```

Rescaling keeps the Lipschitz constant $1$ for the maximum norm, which is at most the $\ell^p$ norm,
and the minimizers have coordinates of absolute value at most $\rho/3$, so they lie in $B_p$. An
$\varepsilon$-minimizer over $B_p$ is therefore a global $\varepsilon$-minimizer, and it rescales to
an $(\varepsilon/\rho)$-minimizer of $f_S$. The rescaled oracle is emulated by the oracle of Section
IV.B, and Theorem IV.2 applies with $\varepsilon/\rho \lt 8^{-M}$.

## Arbitrary local oracles

Section VI extends the lower bounds to all local oracles. Its tool is an oracle that reveals as much
as a local oracle possibly can.

```{prf:definition} Maximal oracle
:label: def-nonsmooth-oracle-complexity-maximal
:enumerator: VI.1

For a family of functions $(f_i)_{i \in I}$, the maximal oracle answers the query $x$ for the
instance $i$ with the set of instances $j$ with $f_j = f_i$ near $x$.
```

```{prf:lemma} Maximal oracle
:label: lem-nonsmooth-oracle-complexity-maximal
:enumerator: VI.2

The maximal oracle is local, and every local oracle is emulated by it, with the identity as query
translation.
```

Instances that agree near $x$ have the same set of instances agreeing with them near $x$. A local
oracle takes the same value at all instances of this set, so evaluating it at any of them recovers
its answer.

The paper then shifts the hard functions by random perturbations, so that with probability one no
query hits a point where the function is not locally linear (Lemmas VI.4 and VI.6). At the other
points the maximal oracle reveals no more than the single-coordinate oracle, which gives Theorems
VI.3 and VI.5 and Proposition VI.7. These arguments need families of instances with continuous
random perturbations and are not formalized.

:::{note}
**Differences from the paper.**
- Algorithms are deterministic query trees, and the prior on the instances is arbitrary. A
  randomized algorithm is a probability distribution over query trees; its expected number of
  queries and its error probability are the averages over the trees.
- Entropies are in nats. Since the bound is homogeneous in the base of the logarithm, dividing by
  $\log 2$ gives the paper's bits.
- The Fano term is $P_e \log(|F| - 1)$, slightly better than the paper's $P_e \log |F|$.
- Section IV: the hard functions are defined on the whole space and queries may be arbitrary. The
  one-dimensional oracle answers a one-sided derivative, the one at which the function increases,
  and the emulations ask for all bits of the greedy paths, which can reveal more than the paper's
  queries. The single-coordinate oracle uses the least coordinate attaining the maximum; the paper's
  convention would answer $0 \cdot e_1$ at a minimizer.
- Lemma III.1 in probability assumes $P_e \le 1/2$, where the binary entropy is increasing.
- Section V: the hard functions are defined on $\mathbb{R}^n$, queries may be arbitrary, and
  $\varepsilon$-minimizers are taken over $B_p$. The standard basis is used for all $p \ge 1$ (see
  the errata above). The oracle answers the least coordinate attaining the maximum and its sign.
  Proposition V.5 is stated with the explicit condition $\varepsilon \lt n^{-1/p} 8^{-M}$, and the
  lower bounds of Section V are stated in expectation.
:::

## Coverage

This entry covers Lemma III.1 and Proposition III.3 in expectation and in probability, Lemma III.5,
Section IV (Lemmas IV.3 to IV.7, Theorem IV.2), Section V with the standard basis (Lemmas V.3 and
V.4, Theorem V.1, Proposition V.5), including the locality of the oracles, and Definition VI.1 and
Lemma VI.2. Not covered are Theorem V.1 for $1 \le p \lt 2$ with the rate $\varepsilon^{-2}$, whose
proof fails (see the errata), Remark V.6, and the perturbation arguments of Section VI (Theorems
VI.3 and VI.5, Lemmas VI.4 and VI.6, Proposition VI.7).

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/OracleComplexity/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/nonsmooth-oracle-complexity.md
```
