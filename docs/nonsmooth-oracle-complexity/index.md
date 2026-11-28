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
[@braun2017lower], currently the information-theoretic lower bound (Lemma III.1, in expectation) and
oracle emulation (Lemma III.5); numbers refer to the arXiv version.
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

:::{note}
**Differences from the paper.**
- Algorithms are deterministic query trees, and the prior on the instances is arbitrary. A
  randomized algorithm is a probability distribution over query trees; its expected number of
  queries and its error probability are the averages over the trees.
- Entropies are in nats. Since the bound is homogeneous in the base of the logarithm, dividing by
  $\log 2$ gives the paper's bits.
- The Fano term is $P_e \log(|F| - 1)$, slightly better than the paper's $P_e \log |F|$.
:::

## Coverage

This entry covers the bound in expectation of Lemma III.1 and Lemma III.5. Not covered yet are the
bound in probability of Lemma III.1, the string guessing problem (Proposition III.3), and the lower
bounds for the box (Section IV), for $\ell^p$-balls (Section V) and for arbitrary local oracles
(Section VI).

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/OracleComplexity/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/nonsmooth-oracle-complexity.md
```
