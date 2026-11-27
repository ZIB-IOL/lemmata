---
title: "An information diffusion Fano inequality"
numbering:
  headings: false
---

```{include} ../_generated/provenance/information-diffusion-fano.md
```

:::{note}
This entry formalizes the note *An information diffusion Fano inequality* by Gábor Braun and
Sebastian Pokutta [@braun2015information]; numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Proposition 2.1 for $\alpha < 1$.** Inequality (2) fails for orders $\alpha < 1$. For the
two-point distributions $P = \mathrm{Bern}(1/2)$ and $Q = \mathrm{Bern}(1/4)$, the event
$R = \{1\}$, $p_{\min} = p_{\max} = 1/4$ and $\alpha = 1/2$, the bracket in (2) equals $1/2$, so (2)
claims $P(R) \le (1/2)^2 = 1/4$, while $P(R) = 1/2$. The last step of the proof, marked "by Eq.
(4)", needs $P(R)^\alpha + (1 - P(R))^\alpha \le 1$, which holds only for $\alpha \ge 1$. The
corrected statement below divides $P(R)^\alpha$ by $P(R)^\alpha + (1 - P(R))^\alpha$; for
$\alpha > 1$ it implies (2), which is formalized as stated.

**Corollary 2.4.** The left-hand side of (6) should be $P[R]$, as in (5), not $P[\neg R]$. For
$X$ uniform on four values, $Y_1$ independent of $X$, $\hat X$ constant and $R = \{X = \hat X\}$, so
that $I(X; Y_1) = \beta = 0$ and $p_{\min} = p_{\max} = 1/4$, the right-hand side of (6) is
$(H(1/4) + \log(3/4))/\log 3 = 1/4$, while $P[\neg R] = 3/4$.
:::

Fano's inequality is a standard tool for lower bounds in statistics and optimization: a hidden
random variable $X$ can be reconstructed from observations $Y$ only if $Y$ carries enough
information about $X$. The setup is a Markov chain $X \to Y \to \hat X$, where the reconstruction
$\hat X$ depends on $X$ only through $Y$. The note replaces the usual reconstruction event
$\hat X = X$ by an arbitrary relation $R$ of acceptable reconstructions, and derives the whole
family of Fano inequalities from one elementary inequality between two distributions. Logarithms
are natural, $D$ is the relative entropy (Kullback–Leibler divergence) of Mathlib, and
$H(p) = -p\log p - (1 - p)\log(1 - p)$ is the binary entropy.

## Relative entropy and mutual information

```{prf:definition} Mutual information
:label: def-information-diffusion-fano-mutual-info
:nonumber:

For a joint law $\mu$ of $(X, Y)$ with marginals $\mu_X$ and $\mu_Y$, the mutual information is
$I(X; Y) = D(\mu \| \mu_X \otimes \mu_Y)$.
```

```{prf:definition} Markov chain
:label: def-information-diffusion-fano-chain
:nonumber:

For a joint law $\mu$ of $(X, Y)$ and a Markov kernel $\kappa$ from the values of $Y$ to those of
$\hat X$, the joint law of $(X, \hat X)$ for the Markov chain $X \to Y \to \hat X$ is the image of
$\mu$ under $(x, y) \mapsto \delta_x \otimes \kappa(y)$.
```

## The information diffusion inequality

```{prf:proposition} Information diffusion Fano inequality, $\alpha = 1$
:label: prop-information-diffusion-fano-kl
:enumerator: 2.1

Let $P$ and $Q$ be probability distributions on the same space and $R$ an event with
$p_{\min} \le Q(R) \le p_{\max}$, where $0 \le p_{\min}$, $0 < p_{\max}$ and
$p_{\min} + p_{\max} < 1$. Then
$$
P(R) \le \frac{D(P \| Q) + H(P(R)) + \log(1 - p_{\min})}{\log\bigl((1 - p_{\min})/p_{\max}\bigr)}.
$$
```

The relative entropy splits over $R$ and its complement, and on each part it is at least
$p\log(p/q) + q - p$, where $p$ and $q$ are the masses of the part under $P$ and $Q$. Summing gives
the data processing bound $d(P(R) \| Q(R)) \le D(P \| Q)$ for the binary relative entropy $d$, and
$d(p \| q) + H(p) = p\log(1/q) + (1 - p)\log(1/(1 - q))$ is at least
$p\log(1/p_{\max}) + (1 - p)\log(1/(1 - p_{\min}))$.

## Rényi divergences

```{prf:definition} Hellinger integral and Rényi divergence
:label: def-information-diffusion-fano-hellinger
:nonumber:

For $\alpha > 0$, the Hellinger integral of order $\alpha$ is $\int (dP/dQ)^\alpha\, dQ$; for
$\alpha < 1$ the part of $P$ that is singular to $Q$ does not contribute, and for $\alpha > 1$ it is
used with $P \ll Q$.
```

```{prf:definition} Rényi divergence
:label: def-information-diffusion-fano-renyi
:nonumber:

For $\alpha \ne 1$, $D_\alpha(P \| Q) = \log\bigl(\int (dP/dQ)^\alpha\, dQ\bigr)/(\alpha - 1)$.
```

```{prf:definition} Binary Rényi entropy
:label: def-information-diffusion-fano-renyi-entropy
:nonumber:

For $\alpha \ne 1$, $H_\alpha(p) = \log(p^\alpha + (1 - p)^\alpha)/(1 - \alpha)$.
```

```{prf:proposition} Information diffusion Fano inequality, $\alpha \ne 1$, corrected
:label: prop-information-diffusion-fano-renyi
:enumerator: 2.1

Under the assumptions of Proposition 2.1, let $0 < \alpha \ne 1$, with $P \ll Q$ if $\alpha > 1$,
and let the Hellinger integral of order $\alpha$ be positive and finite. With $p = P(R)$,
$A = D_\alpha(P \| Q) + H_\alpha(p) + \log(1 - p_{\min})$ and $B = (1 - p_{\min})/p_{\max}$,
$$
\frac{p^\alpha}{p^\alpha + (1 - p)^\alpha} \le \frac{e^{(\alpha - 1)A} - 1}{B^{\alpha - 1} - 1}.
$$
```

```{prf:proposition} Information diffusion Fano inequality, $\alpha > 1$
:label: prop-information-diffusion-fano-renyi-gt-one
:enumerator: 2.1

Under the assumptions of Proposition 2.1, let $\alpha > 1$, $P \ll Q$, and let the Hellinger
integral of order $\alpha$ be finite. Then
$P(R) \le \bigl((e^{(\alpha - 1)A} - 1)/(B^{\alpha - 1} - 1)\bigr)^{1/\alpha}$.
```

Hölder's inequality on $R$ and on its complement compares the Hellinger integral with its
two-point version $q^{1-\alpha}p^\alpha + (1 - q)^{1-\alpha}(1 - p)^\alpha$, where $q = Q(R)$: it is
at least that for $\alpha > 1$ and at most that for $\alpha < 1$, so $D_\alpha(P \| Q) \ge
d_\alpha(P(R) \| Q(R))$ in both cases. Since $e^{(\alpha - 1)A}$ is the Hellinger integral times
$(1 - p_{\min})^{\alpha - 1}/(p^\alpha + (1 - p)^\alpha)$, both cases reduce to comparing
$p^\alpha B^{\alpha - 1} + (1 - p)^\alpha$ with the Hellinger integral times
$(1 - p_{\min})^{\alpha - 1}$. For $\alpha > 1$, $p^\alpha + (1 - p)^\alpha \le 1$ gives the form of
the paper.

## Fano inequality for arbitrary relations

```{prf:proposition} Fano inequality for arbitrary relations
:label: prop-information-diffusion-fano-relation
:enumerator: 2.2

Let $X \to Y \to \hat X$ be a Markov chain and $R$ a measurable relation between values of $X$ and
of $\hat X$, and let $p_{\min} \le P[(X, \hat x) \in R] \le p_{\max}$ for every $\hat x$, where
$0 \le p_{\min}$, $0 < p_{\max}$ and $p_{\min} + p_{\max} < 1$. If $I(X; Y) < \infty$, then
$$
P[R] \le \frac{I(X; \hat X) + H(P[R]) + \log(1 - p_{\min})}{\log\bigl((1 - p_{\min})/p_{\max}\bigr)}
  \le \frac{I(X; Y) + H(P[R]) + \log(1 - p_{\min})}{\log\bigl((1 - p_{\min})/p_{\max}\bigr)}.
$$
```

The second inequality is data processing for the relative entropy: the joint law of
$(X, \hat X)$ and the product of its marginals are the images of the joint law of $(X, Y)$ and the
product of its marginals under the same Markov kernel. The first is Proposition 2.1 with $P$ the
joint law of $(X, \hat X)$ and $Q$ the product of its marginals, under which $R$ has probability
$\int P[(X, \hat x) \in R]\, dP_{\hat X}(\hat x) \in [p_{\min}, p_{\max}]$.

## Entropy of finite random variables

For random variables with finitely many values the relative entropy is a finite sum, and mutual
information can be written with entropies.

```{prf:definition} Entropy
:label: def-information-diffusion-fano-entropy
:nonumber:

For a law $P$ on a finite set, $H(X) = -\sum_a P(a)\log P(a)$.
```

```{prf:definition} Conditional entropy
:label: def-information-diffusion-fano-cond-entropy
:nonumber:

For a joint law of $(X, \hat X)$ on finite sets, $H(X \mid \hat X) = H(X, \hat X) - H(\hat X)$.
```

```{prf:theorem} Mutual information and entropy
:label: thm-information-diffusion-fano-mutual-info-entropy
:nonumber:

For a joint law of $(X, \hat X)$ on finite sets, $I(X; \hat X)$ is finite and
$I(X; \hat X) = H(X) - H(X \mid \hat X)$.
```

```{prf:proposition} Entropy of the uniform law
:label: prop-information-diffusion-fano-entropy-uniform
:nonumber:

The uniform law on a finite set $\mathcal X$ has entropy $\log |\mathcal X|$.
```

On a finite set with all singletons measurable, the Radon–Nikodym derivative at a point of
positive mass is the ratio of the masses, so $D(P \| Q) = \sum_b P(b)\log(P(b)/Q(b))$. For a joint
law and the product of its marginals this is $H(X) + H(\hat X) - H(X, \hat X)$.

## Entropy versions

Inequality (5) rearranged in terms of $I(X; \hat X) = H(X) - H(X \mid \hat X)$ gives entropy
versions; the condition $p_{\min} + p_{\max} < 1$ is no longer needed.

```{prf:corollary} Entropy version of the Fano inequality
:label: cor-information-diffusion-fano-entropy
:enumerator: 2.3

Let $X$ and $\hat X$ take finitely many values, and let $R$ be a relation with
$p_{\min} \le P[(X, \hat x) \in R] \le p_{\max}$ for every $\hat x$, where $0 \le p_{\min} < 1$ and
$0 < p_{\max}$. Then
$$
H(X \mid \hat X) \le H(X) + \log p_{\max} + H(P[\neg R]) +
  P[\neg R]\log\frac{1 - p_{\min}}{p_{\max}}.
$$
```

```{prf:corollary} Distance-based Fano inequality
:label: cor-information-diffusion-fano-distance-entropy
:enumerator: 2.5

Let $X$ be uniform on a finite set $\mathcal X$ and $\hat X \in \mathcal X$, and let
$N_{\min} \le |\{x \mid \rho(x, \hat x) \le t\}| \le N_{\max}$ for every $\hat x$, with
$0 < N_{\max}$ and $N_{\min} < |\mathcal X|$. Then
$$
H(X \mid \hat X) \le H(P_t) + P_t\log\frac{|\mathcal X| - N_{\min}}{N_{\max}} + \log N_{\max}.
$$
```

Corollary 2.5 is Corollary 2.3 with $p_{\min} = N_{\min}/|\mathcal X|$ and
$p_{\max} = N_{\max}/|\mathcal X|$, since $H(X) = \log|\mathcal X|$ for uniform $X$.

## Independent samples

If $Y = (Y_1, \dots, Y_n)$ consists of samples that are i.i.d. given $X$, the mutual information
grows at most linearly in $n$.

```{prf:corollary} Fano inequality for independent samples
:label: cor-information-diffusion-fano-samples
:enumerator: 2.4

Let $X$ take finitely many values, let $Y_1, \dots, Y_n$ take finitely many values and be i.i.d.
with law $\eta(x)$ given $X = x$, and let $\hat X$ be drawn from a Markov kernel applied to $Y$. Let
$R$, $p_{\min}$ and $p_{\max}$ be as in Proposition 2.2, and let $\eta(x) \ll \eta(x')$ and
$D(\eta(x) \| \eta(x')) \le \beta$ for all $x, x'$. Then
$$
P[R] \le \frac{n\, I(X; Y_1) + H(P[R]) + \log(1 - p_{\min})}
    {\log\bigl((1 - p_{\min})/p_{\max}\bigr)}
  \le \frac{n\beta + H(P[R]) + \log(1 - p_{\min})}{\log\bigl((1 - p_{\min})/p_{\max}\bigr)}.
$$
```

Let $Q$ be the product of the laws of the $Y_i$, and $P_x$ the law of $Y$ given $X = x$. Then
$\sum_x P(X = x)\, D(P_x \| Q) = I(X; Y) + D(P_Y \| Q)$, and since $D(P_Y \| Q) \ge 0$,
$I(X; Y) \le \sum_x P(X = x)\, D(P_x \| Q) = n\, I(X; Y_1)$, the last step because $P_x$ and $Q$
are products. Concavity of the logarithm gives
$D(\eta(x) \| P_{Y_1}) \le \sum_{x'} P(X = x')\, D(\eta(x) \| \eta(x'))$, hence
$I(X; Y_1) \le \beta$.

## Special cases

For a function $\rho$ and a radius $t$, the relation $\rho(x, \hat x) \le t$ with $p_{\min} = 0$
gives the distance-based and continuous Fano inequalities of Duchi and Wainwright, with
$P_t = P[\rho(X, \hat X) > t]$.

```{prf:corollary} Distance-based Fano inequality
:label: cor-information-diffusion-fano-distance
:enumerator: 2.6

Let $X \to Y \to \hat X$ be a Markov chain with $X$ uniform on a finite set $\mathcal X$ and
$\hat X \in \mathcal X$, and let $0 < N < |\mathcal X|$ with
$|\{x \mid \rho(x, \hat x) \le t\}| \le N$ for every $\hat x$. If $I(X; Y) < \infty$, then
$$
P_t \ge 1 - \frac{I(X; Y) + H(P_t)}{\log(|\mathcal X|/N)}.
$$
```

```{prf:corollary} Continuous Fano inequality
:label: cor-information-diffusion-fano-continuous
:enumerator: 2.7

Let $X \to Y \to \hat X$ be a Markov chain with $X$ uniform on a measurable set $S$ of finite
positive volume, let $\rho$ be measurable, and let $0 < V < \operatorname{vol}(S)$ with
$\operatorname{vol}(\{x \mid \rho(x, \hat x) \le t\} \cap S) \le V$ for every $\hat x$. If
$I(X; Y) < \infty$, then
$$
P_t \ge 1 - \frac{I(X; Y) + \log 2}{\log(\operatorname{vol}(S)/V)}.
$$
```

In the continuous case the binary entropy is bounded by $\log 2$.

:::{note}
**Differences from the paper.** The paper takes $\rho$ symmetric and counts the balls
$\{\hat x \mid \rho(x, \hat x) \le t\}$; the formal statements bound the sections
$\{x \mid \rho(x, \hat x) \le t\}$ that the proof uses, which is the same for symmetric $\rho$, and
take any bound $N$ or $V$ in place of the maximum or supremum. Corollaries 2.3 and 2.5 hold for
any joint law of $(X, \hat X)$ with finitely many values; the Markov chain is not needed for them.
Corollary 2.4 is stated for finitely many values of $X$ and of the samples, with the joint laws
given by their point masses, and with any bound $\beta$ on the relative entropies.
:::

## Coverage

All results of the note are formalized: Propositions 2.1 and 2.2 and Corollaries 2.3 to 2.7.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FanoDiffusion/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/information-diffusion-fano.md
```
