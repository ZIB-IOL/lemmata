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
take any bound $N$ or $V$ in place of the maximum or supremum.
:::

## Not yet covered

Proposition 2.1 for Rényi divergences of order $\alpha \ne 1$, the entropy versions
(Corollaries 2.3 and 2.5) and the version for independent samples (Corollary 2.4) are not yet
covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FanoDiffusion/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/information-diffusion-fano.md
```
