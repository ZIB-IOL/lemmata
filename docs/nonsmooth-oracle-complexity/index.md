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
[@braun2017lower], currently the information-theoretic lower bound (Lemma III.1, in expectation),
the string guessing problem (Proposition III.3), oracle emulation (Lemma III.5) and the
one-dimensional lower bound for nonsmooth convex optimization (Section IV.A); numbers refer to the
arXiv version.
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
most $\log |F|$. With $\log |F|$ in place of $H(F)$ the claim holds, and for the uniform prior,
which is how the paper uses it, the two agree.
:::

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

The oracle answers the query $x$ with the value $f_S(x)$ and the slope
$2^{-j} \operatorname{sign}(x - c_j(S))$ of the first piece $j$ that attains the maximum.
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
$\varepsilon \lt 8^{-M}$, as stated here.
:::

```{prf:lemma} Emulation by string guessing
:label: lem-nonsmooth-oracle-complexity-box-emulation
:enumerator: IV.5

The oracle of the hard functions is emulated by the string guessing oracle on strings of length $M$.
```

The query asks for the bits of the greedy path towards $x$, and the answer reveals the first bit $k$
where $S$ leaves it. Then $x$ lies outside the interval of the first $k + 1$ bits of $S$, where
every deeper piece lies below the piece of depth $k + 1$, so the value and the slope of the first
maximal piece depend only on the first $k + 1$ bits of $S$, which the answer determines.

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

:::{note}
**Differences from the paper.**
- Algorithms are deterministic query trees, and the prior on the instances is arbitrary. A
  randomized algorithm is a probability distribution over query trees; its expected number of
  queries and its error probability are the averages over the trees.
- Entropies are in nats. Since the bound is homogeneous in the base of the logarithm, dividing by
  $\log 2$ gives the paper's bits.
- The Fano term is $P_e \log(|F| - 1)$, slightly better than the paper's $P_e \log |F|$.
- Section IV.A: the oracle answers the slope of the first maximal piece, and the emulation asks for
  all $M$ bits of the greedy path, which can reveal more than the paper's query. The locality of the
  oracle, part of Lemma IV.5, is not formalized. Queries may be any real numbers, and the hard
  functions are defined on the whole line.
:::

## Coverage

This entry covers the bound in expectation of Lemma III.1, Proposition III.3, Lemma III.5 and the
one-dimensional case of Section IV (Lemmas IV.3 and IV.5, Theorem IV.2). Not covered yet are the
bounds in probability of Lemma III.1 and Proposition III.3, the locality of the oracle in Lemma
IV.5, the multidimensional case (Section IV.B), the lower bounds for $\ell^p$-balls (Section V) and
for arbitrary local oracles (Section VI).

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/OracleComplexity/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/nonsmooth-oracle-complexity.md
```
