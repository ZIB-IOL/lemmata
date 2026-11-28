---
title: "Frank–Wolfe with simple steps for generalized self-concordant functions"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-generalized-self-concordant.md
```

:::{note}
This entry formalizes the paper *Scalable Frank–Wolfe on Generalized Self-concordant Functions via
Simple Steps* by Alejandro Carderera, Mathieu Besançon and Sebastian Pokutta [@carderera2021simple],
currently the monotonic Frank–Wolfe algorithm and its convergence rates (Algorithm 1, Theorems 2.4
and 2.6) the improved rates of Frank–Wolfe with backtracking (Theorems 2.11, 2.15 and 2.16), and the
linear rates of away-step Frank–Wolfe and blended pairwise conditional gradients with backtracking
over polytopes (Theorem 3.2); numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Lemma 2.14.** The lemma turns contractions $h_t - h_{t+1} \ge h_t \min\{c_1, c_2 h_t^\alpha\}$
into rates, with $t_0 = \max\{1, \lfloor \log_{1-c_1}((c_1/c_2)^{1/\alpha}/c_0) \rfloor\}$ and the
bound $(c_1/c_2)^{1/\alpha}/(1 + c_1\alpha(t - t_0))^{1/\alpha}$ for $t > t_0$. This bound can fail:
for $c_0 = 2$, $c_1 = 1/2$, $c_2 = 1$ and $\alpha = 1$, the sequence $h_1 = 2$,
$h_{t+1} = h_t(1 - \min\{1/2, h_t\})$ satisfies the hypotheses with equality, $t_0 = 2$, and
$h_3 = 1/2$ exceeds the bound $1/3$. The lemma holds with
$t_0 = \max\{\lfloor \log_{1-c_1}((c_1/c_2)^{1/\alpha}/c_0) \rfloor + 2, 1\}$, the first bound for
$t < t_0$ and the second for $t \ge t_0$; this is Lemma 2.21 of [Conditional gradient methods:
smoothness, scaling and linear rates](../conditional-gradient-basics/index.md), where the book's
version has a similar slip. Theorems 2.15 and 2.16, which use the lemma, are formalized with this
$t_0$.
:::

Many objectives in statistics and machine learning, such as the logistic loss or log-barriers, are
neither globally smooth nor finite everywhere. They are *generalized self-concordant*: a function
$f$ with an open domain is $(M, \nu)$-generalized self-concordant if its third derivative is bounded
by its Hessian,

$$
|\langle D^3 f(x)[w] u, u \rangle| \le M \|u\|_{\nabla^2 f(x)}^2 \|w\|_{\nabla^2 f(x)}^{\nu - 2}
\|w\|_2^{3 - \nu}.
$$

The standard analyses of the Frank–Wolfe algorithm need a smoothness constant, and a step of the
Frank–Wolfe algorithm with the simple step size $\gamma_t = 2/(t + 2)$ can leave the domain. The
paper shows that a tiny modification suffices: reject a step whenever it leaves the domain or
increases the objective.

## Monotonic Frank–Wolfe

```{prf:definition} Monotonic Frank–Wolfe
:label: def-frank-wolfe-generalized-self-concordant-run
:nonumber:

A run of monotonic Frank–Wolfe on $\mathcal{X}$ for $f$ with domain $\operatorname{dom} f$ starts at
$x_0 \in \mathcal{X} \cap \operatorname{dom} f$, picks a Frank–Wolfe vertex $v_t$ for
$\nabla f(x_t)$, and sets $x_{t+1} = x_t + \gamma_t (v_t - x_t)$ with $\gamma_t = 2/(t + 2)$ if this
point lies in $\operatorname{dom} f$ and does not increase $f$; otherwise $x_{t+1} = x_t$.
```

Generalized self-concordance controls the objective near every point of its domain: by results of
Sun and Tran-Dinh (Proposition 2.1 and Lemma 2.3 of the paper), a step that is short in the local
norm stays in the domain and satisfies a quadratic upper bound with the factor $\omega_\nu(1/2)$
(Remark 2.2). Since the iterates of monotonic Frank–Wolfe stay in the sublevel set $\mathcal{L}_0$
of $x_0$, on which the Hessian is bounded by $L$, this yields the following property from the
iteration $T_\nu$ on, with $K = L D^2 \omega_\nu(1/2)$; the formal statements assume it.

```{prf:definition} Local descent
:label: def-frank-wolfe-generalized-self-concordant-descent
:nonumber:

$f$ has the local descent property with step bound $\bar{\gamma}$ and constant $K$ if for every
$y \in \mathcal{X} \cap \operatorname{dom} f$ with $f(y) \le f(x_0)$, every $w \in \mathcal{X}$ and
every $\gamma \in [0, \bar{\gamma}]$, the point $y + \gamma (w - y)$ lies in $\operatorname{dom} f$
and $f(y + \gamma (w - y)) \le f(y) + \gamma \langle \nabla f(y), w - y \rangle + \gamma^2 K$.
```

```{prf:theorem} Primal gap of monotonic Frank–Wolfe
:label: thm-frank-wolfe-generalized-self-concordant-rate
:enumerator: 2.4

Let $f$ be convex on $\mathcal{X} \cap \operatorname{dom} f$ with a minimizer $x^\star$ there, and
let it have the local descent property with step bound $2/(T + 2)$ and constant $K \ge 0$. Every run
of monotonic Frank–Wolfe satisfies, for all $t \ge T$,

$$
f(x_t) - f(x^\star) \le \frac{4 (T + 1)}{t + 1} \max\{f(x_0) - f(x^\star), K\}.
$$
```

The iterates stay in the sublevel set, and from $T$ on the candidate point obeys the quadratic
bound. If $\gamma_t h_t > \gamma_t^2 K$ for the primal gap $h_t$, the candidate decreases $f$ and is
accepted, and $h_{t+1} \le (1 - \gamma_t) h_t + \gamma_t^2 K$; otherwise $h_t \le \gamma_t K$
already, and monotonicity carries the bound to $t + 1$.

```{prf:theorem} Frank–Wolfe gap of monotonic Frank–Wolfe
:label: thm-frank-wolfe-generalized-self-concordant-gap
:enumerator: 2.6

Under the assumptions of Theorem 2.4 with $T \ge 1$, for every $N \ge T + 6$ some iteration
$1 \le t \le N$ has Frank–Wolfe gap

$$
g_t \le \frac{18 N}{N - T} \left( \frac{T + 1}{2T + N - 3} + \frac{2N - 2T + 3}{(2T + N)^2} \right)
\max\{f(x_0) - f(x^\star), K\} = O(1/N).
$$
```

Consider the iterations between $T + \lceil (N - T)/3 \rceil - 2$ and $N - 2$. Either one of them
has $g_t \le \gamma_t K$, or every step there is accepted with progress at least
$\gamma_t g_t - \gamma_t^2 K$; if all gaps exceeded the bound, the accumulated progress would make
the primal gap negative.

## Frank–Wolfe with backtracking

For improved rates the paper uses the adaptive step size of Pedregosa, Negiar, Askari and Jaggi: a
backtracking line search finds a smoothness estimate $L_t$ and the step
$\gamma_t = \min\{1, g_t/(L_t\|v_t - x_t\|^2)\}$ minimizing the quadratic model, with sufficient
decrease. The estimates stay below $\tilde{L} = \max\{\tau L, L_{-1}\}$ for the backtracking factor
$\tau$ and the initial estimate $L_{-1}$.

```{prf:definition} Frank–Wolfe with backtracking
:label: def-frank-wolfe-generalized-self-concordant-backtracking
:nonumber:

A run of Frank–Wolfe with backtracking picks a Frank–Wolfe vertex $v_t$, a smoothness estimate
$0 < L_t \le \tilde{L}$ and the step $\gamma_t = \min\{1, g_t/(L_t\|v_t - x_t\|^2)\}$, and sets
$x_{t+1} = x_t + \gamma_t(v_t - x_t) \in \operatorname{dom} f$ with
$f(x_{t+1}) \le f(x_t) - \gamma_t g_t + \frac{L_t \gamma_t^2}{2}\|v_t - x_t\|^2$.
```

Since $\gamma_t$ minimizes the quadratic model with $L_t \le \tilde{L}$, every step does at least as
well as each $s \in [0, 1]$ in the model with $\tilde{L}$, and the objective decreases; the iterates
stay in the sublevel set $\mathcal{L}_0$, where generalized self-concordance with a domain
containing no straight line makes $f$ strongly convex with some modulus $\mu > 0$ (Proposition 2.9,
a result of Sun and Tran-Dinh). The formal statements assume this local strong convexity.

```{prf:theorem} Minimizer in the interior
:label: thm-frank-wolfe-generalized-self-concordant-interior
:enumerator: 2.11

Let $\mathcal{X}$ be compact and convex with diameter $D$, let $f$ be convex with a minimizer
$x^\star$ on $\mathcal{X} \cap \operatorname{dom} f$ and $\mu$-strongly convex on $\mathcal{L}_0$,
and let the ball of radius $r > 0$ around $x^\star$ lie in $\mathcal{X}$. Every run of Frank–Wolfe
with backtracking satisfies

$$
f(x_t) - f(x^\star) \le \left(1 - \frac{1}{2}\min\left\{1, \frac{\mu r^2}{\tilde{L}
D^2}\right\}\right)^t
(f(x_0) - f(x^\star)).
$$
```

The ball gives $g_t \ge r\|\nabla f(x_t)\|$ (Proposition 2.10), and strong convexity at the pair
$(x_t, x^\star)$ gives $f(x_t) - f(x^\star) \le \|\nabla f(x_t)\|^2/(2\mu)$.

Over uniformly convex sets the scaling inequality $\kappa\|\nabla f(x)\|\,\|x - v\|^q \le g(x)$
(Proposition 2.13) replaces the ball, and the contraction lemma turns the per-step progress into
rates.

```{prf:theorem} Uniformly convex sets, gradients bounded away from zero
:label: thm-frank-wolfe-generalized-self-concordant-uc-gradient
:enumerator: 2.15

Let $\mathcal{X}$ be compact, convex and $(\kappa, q)$-uniformly convex with $q \ge 2$, and let $f$
be convex with a minimizer on $\mathcal{X} \cap \operatorname{dom} f$ and $\|\nabla f\| \ge c > 0$
there. Every run of Frank–Wolfe with backtracking satisfies, with $h_t = f(x_t) - f(x^\star)$: for
$q = 2$, $h_t \le (1 - \frac{1}{2}\min\{1, \kappa c/\tilde{L}\})^t h_0$; for $q > 2$, with
$\tau = (\tilde{L}^q/(\kappa c)^2)^{1/(q-2)}$ and
$t_0 = \max\{\lfloor \log_{1/2}(\tau/h_0) \rfloor + 2, 1\}$, $h_t \le h_0 2^{1-t}$ for
$1 \le t < t_0$ and $h_t \le \tau/(1 + (q-2)(t - t_0)/(2q))^{q/(q-2)}$ for $t \ge t_0$.
```

```{prf:theorem} Uniformly convex sets, local strong convexity
:label: thm-frank-wolfe-generalized-self-concordant-uc-strong
:enumerator: 2.16

Let $\mathcal{X}$ be compact, convex and $(\kappa, q)$-uniformly convex with $q \ge 2$, and let $f$
be convex with a minimizer on $\mathcal{X} \cap \operatorname{dom} f$ and $\mu$-strongly convex on
$\mathcal{L}_0$. Every run of Frank–Wolfe with backtracking satisfies, with
$\tau = (\tilde{L}^q/(\kappa^2\mu))^{1/(q-1)}$ and
$t_0 = \max\{\lfloor \log_{1/2}(\tau/h_0) \rfloor + 2, 1\}$, $h_t \le h_0 2^{1-t}$ for
$1 \le t < t_0$ and $h_t \le \tau/(1 + (q-1)(t - t_0)/(2q))^{q/(q-1)}$ for $t \ge t_0$, which is
$O(t^{-q/(q-1)})$.
```

## Away-step Frank–Wolfe over polytopes

Over a polytope $\mathcal{X} = \operatorname{conv} V$, away steps remove the dependence on the
position of the minimizer. Away-step Frank–Wolfe keeps an active set $\mathcal{S}_t \subseteq V$
with weights representing $x_t$; at each step it compares the Frank–Wolfe gap with the away gap
$\langle \nabla f(x_t), a_t - x_t \rangle$ for the worst active vertex $a_t$, moves toward $v_t$ or
away from $a_t$, and uses the backtracking line search with step sizes capped at $1$ or at the
weight ratio $\lambda_t(a_t)/(1 - \lambda_t(a_t))$.

```{prf:definition} Away-step Frank–Wolfe with backtracking
:label: def-frank-wolfe-generalized-self-concordant-away
:nonumber:

A run starts at a vertex $x_0 \in \operatorname{dom} f$ with active set $\{x_0\}$, and every step is
an away-step Frank–Wolfe step, with active set and weights updated as in the [away-step
entry](../away-step-frank-wolfe/index.md), whose step size is the short step for a smoothness
estimate $0 < L_t \le \tilde{L}$ clipped at the maximal step size, with
$x_{t+1} \in \operatorname{dom} f$ and sufficient decrease.
```

```{prf:theorem} Away-step Frank–Wolfe
:label: thm-frank-wolfe-generalized-self-concordant-away
:enumerator: 3.2

Let $x^\star$ minimize $f$ on $\operatorname{conv} V \cap \operatorname{dom} f$, let $f$ be
$\mu$-strongly convex on $\mathcal{L}_0$, and let $\delta > 0$ be the pyramidal width of
$\operatorname{conv} V$, whose diameter is $D$. Every run of away-step Frank–Wolfe with backtracking
satisfies

$$
f(x_t) - f(x^\star) \le
\left(1 - \min\left\{\frac{1}{2}, \frac{\mu\delta^2}{4\tilde{L}D^2}\right\}\right)^{\lceil (t-1)/2
\rceil}
(f(x_0) - f(x^\star)).
$$
```

Strong convexity at $(x_t, x^\star)$ and the scaling inequality of the pyramidal width give
$f(x_t) - f(x^\star) \le \langle \nabla f(x_t), a_t - v_t \rangle^2/(2\mu\delta^2)$, and the chosen
gap is at least half of $\langle \nabla f(x_t), a_t - v_t \rangle$. A step whose step size is not
capped therefore contracts the primal gap, as does a full Frank–Wolfe step; an away step with
maximal step size drops $a_t$ from the active set without increasing $f$. Since the active set
starts with one vertex and every other step adds at most one, at least half of the steps contract.

Blended pairwise conditional gradients replace the away step by a pairwise step, which moves weight
from $a_t$ to the best active vertex $s_t$ when the pairwise gap
$\langle \nabla f(x_t), a_t - s_t \rangle$ exceeds the Frank–Wolfe gap, with step sizes capped at
$\lambda_t(a_t)$.

```{prf:definition} Blended pairwise conditional gradients with backtracking
:label: def-frank-wolfe-generalized-self-concordant-pairwise
:nonumber:

A run starts at a vertex $x_0 \in \operatorname{dom} f$ with active set $\{x_0\}$. At each step,
with an away vertex $a_t$ and a local Frank–Wolfe vertex $s_t$ of the active set and a Frank–Wolfe
vertex $v_t$, it takes the pairwise step $x_{t+1} = x_t + \gamma_t(s_t - a_t)$ if
$\langle \nabla f(x_t), a_t - s_t \rangle > \langle \nabla f(x_t), x_t - v_t \rangle$ and the
Frank–Wolfe step otherwise. The step size is the short step for an estimate $0 < L_t \le \tilde{L}$
clipped at $\lambda_t(a_t)$ or $1$, with $x_{t+1} \in \operatorname{dom} f$ and sufficient decrease,
and the active set and the weights are updated as in the [BPCG
entry](../blended-pairwise-conditional-gradients/index.md).
```

```{prf:theorem} Blended pairwise conditional gradients
:label: thm-frank-wolfe-generalized-self-concordant-pairwise
:enumerator: 3.2

Under the hypotheses of the previous theorem, every run of blended pairwise conditional gradients
with backtracking satisfies the same bound.
```

Here $\langle \nabla f(x_t), s_t \rangle \le \langle \nabla f(x_t), x_t \rangle$ makes the chosen
gap at least half of $\langle \nabla f(x_t), a_t - v_t \rangle$ in both cases, and a pairwise step
with maximal step size drops $a_t$.

:::{note}
**Differences from the paper.**
- Generalized self-concordance enters through the local descent property, which the paper derives
  from Proposition 2.1, Remark 2.2 and Lemma 2.3 (results of Sun and Tran-Dinh) with
  $K = L D^2 \omega_\nu(1/2)$ and step bound $2/(T_\nu + 2)$. The theorems hold for every function
  with this property, in real normed spaces, with the domain any convex set.
- $T$ is a natural number; the paper's $T_\nu$ can be $-1$, in which case $T = 0$ serves.
- Theorem 2.6 assumes $T \ge 1$. For $T_\nu \le 0$ the paper's proof can pick the iteration $0$,
  which the minimum over $1 \le t \le N$ excludes, and $2T_\nu + N - 3$ can vanish; since the local
  descent property for a step bound also holds for every smaller bound, $T$ can always be taken at
  least $1$.
- Theorems 2.11 and 2.16 assume strong convexity on the sublevel set, which the paper obtains from
  Proposition 2.9. The bound $f(x_t) - f(x^\star) \le \|\nabla f(x_t)\|^2/(2\mu)$ is proved with the
  constrained minimizer $x^\star$, which lies in the sublevel set; the paper passes through the
  unconstrained minimum, where local strong convexity is not available. Theorem 2.11 keeps the
  minimum with $1$ that the proof gives; the paper drops it, which needs
  $\mu r^2 \le \tilde{L} D^2$. The ball around $x^\star$ need only lie in $\mathcal{X}$.
- In Theorems 2.15 and 2.16 the threshold $t_0$ is the corrected one (see the errata), and the first
  regime reads $h_0 2^{1-t}$ instead of $h_0 2^{-t}$, as the contraction lemma is applied from
  $t = 1$ with $c_0 = h_0$.
- Theorem 3.2 holds for any constant $\delta > 0$ with the scaling property of the pyramidal width,
  in any normed space; its contraction factor is $1 - \min\{1/2, \mu\delta^2/(4\tilde{L}D^2)\}$,
  which is the paper's $1 - \mu\delta^2/(4\tilde{L}D^2)$ whenever $\mu\delta^2 \le 2\tilde{L}D^2$.
  Only strong convexity at the pairs $(x_t, x^\star)$ is used, and no convexity or smoothness
  hypothesis beyond the line search is needed.
- In Algorithm 5 the pairwise direction is $s_t - a_t$ and the pairwise gap is
  $\langle \nabla f(x_t), a_t - s_t \rangle$; the paper writes $a_t - s_t$ and
  $\langle \nabla f(a_t), s_t - a_t \rangle$.
:::

## Coverage

This entry covers Algorithm 1 and Theorems 2.4 and 2.6, and Frank–Wolfe with backtracking with
Theorems 2.11, 2.15 and 2.16. The results of Sun and Tran-Dinh behind the local descent property and
the local strong convexity (Propositions 2.1 and 2.9, Lemma 2.3) and Remark 2.2 are cited, not
formalized; Propositions 2.10 and 2.13 are proved here or in the basics entry. Section 3 is covered:
Theorem 3.2 for both algorithms, and Proposition 3.1, the scaling property, is formalized in the
away-step entry. The stateless step size variant and the experiments are not covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWSelfConcordant/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-generalized-self-concordant.md
```
