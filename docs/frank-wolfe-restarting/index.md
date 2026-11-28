---
title: "Restarting Frank–Wolfe under Hölderian error bounds"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-restarting.md
```

:::{note}
This entry formalizes results of the paper *Restarting Frank–Wolfe: Faster Rates Under Hölderian
Error Bounds* by Thomas Kerdreux, Alexandre d'Aspremont and Sebastian Pokutta
[@kerdreux2018restarting], currently the strong Wolfe gap bounds (Lemmas 2.3 and 3.6), fractional
away-step Frank–Wolfe with scheduled restarts (Propositions 4.1 and 4.2, Theorem 5.1) and the rate
of vanilla Frank–Wolfe over strongly convex sets (Theorem 7.3); numbers refer to the arXiv version.
:::

The Frank–Wolfe algorithm converges at the rate $O(1/t)$ for smooth convex objectives, and its
away-step variant converges linearly over polytopes for strongly convex objectives. A
$(\theta, c)$-Hölderian error bound,
$\operatorname{dist}(x, X^\star) \le c\,(f(x) - f^\star)^\theta$ with $\theta \in [0, 1/2]$,
interpolates between the two: $\theta = 0$ is no information and $\theta = 1/2$ follows from strong
convexity. The paper restarts a fractional version of away-step Frank–Wolfe whenever a computable
optimality measure, the strong Wolfe gap, has dropped by a constant factor; this entry starts with
the properties of that measure.

## The strong Wolfe gap

For an iterate $x$ written as a convex combination of an active set $S$ of vertices, with an away
vertex $a \in \operatorname{argmax}_{y \in S} \langle \nabla f(x), y \rangle$ and a Frank–Wolfe
vertex $v \in \operatorname{argmin}_{z \in \mathcal{C}} \langle \nabla f(x), z \rangle$, the strong
Wolfe gap is $w(x, S) = \langle \nabla f(x), a - v \rangle$, the sum of the away gap
$\langle \nabla f(x), a - x \rangle$ and the Frank–Wolfe gap $\langle \nabla f(x), x - v \rangle$.

```{prf:lemma} The strong Wolfe gap
:label: lem-frank-wolfe-restarting-gap
:enumerator: 2.3

Let $x$ be a convex combination of $S \subseteq \mathcal{V}$ with positive weights, and let $f$ be
convex and differentiable over $\operatorname{conv}(\mathcal{V})$. Then
$f(x) - f^\star \le w(x, S)$, and $w(x, S) = 0$ if and only if $x$ minimizes $f$ over
$\operatorname{conv}(\mathcal{V})$.
```

At a minimizer the Frank–Wolfe gap vanishes, and so does the away gap: the terms
$\langle \nabla f(x), y - x \rangle$, $y \in S$, are nonnegative and their positive combination is
$0$.

```{prf:lemma} Strong Wolfe primal bound
:label: lem-frank-wolfe-restarting-heb
:enumerator: 3.6

Let $f$ be convex and differentiable over $\operatorname{conv}(\mathcal{V})$ with a
$(\theta, c)$-Hölderian error bound, and let $\delta > 0$ have the scaling property of the pyramidal
width. For $x \in \operatorname{conv}(S)$ with $S \subseteq \mathcal{V}$,

$$
f(x) - f^\star \le \Big(\frac{c}{\delta}\Big)^{1/(1-\theta)} w(x, S)^{1/(1-\theta)}.
$$
```

With a minimizer $x^\star$ near the distance from $x$ to $X^\star$, convexity gives
$f(x) - f^\star \le \langle \nabla f(x), x - x^\star \rangle$, the scaling property bounds this by
$w(x, S)\,\|x - x^\star\|/\delta$, and the error bound bounds $\|x - x^\star\|$ by
$c\,(f(x) - f^\star)^\theta$.

## Fractional away-step Frank–Wolfe

Algorithm 1 runs away-step Frank–Wolfe only until the strong Wolfe gap has dropped from $w_0$ to
$e^{-\gamma} w_0$. Instead of comparing the Frank–Wolfe gap with the away gap, it takes the
Frank–Wolfe direction whenever the Frank–Wolfe gap exceeds the fixed threshold $e^{-\gamma} w_0/2$;
while the algorithm runs, the strong Wolfe gap exceeds $e^{-\gamma} w_0$, so either way the
direction $d_t$ satisfies $-\langle \nabla f(x_t), d_t \rangle > e^{-\gamma} w_0/2$.

```{prf:definition} Fractional away-step Frank–Wolfe (Algorithm 1)
:label: def-frank-wolfe-restarting-fractional
:nonumber:

Start from a convex combination $x_0$ of an active set $S_0 \subseteq \mathcal{V}$ and stop once the
strong Wolfe gap $w(x_t, S_t)$ is at most $e^{-\gamma} w_0$. Otherwise take a Frank–Wolfe vertex
$v_t$ and an away vertex $a_t$. If $\langle \nabla f(x_t), x_t - v_t \rangle > e^{-\gamma} w_0/2$,
step towards $v_t$ with exact line search over $[0, 1]$; otherwise step away from $a_t$ with exact
line search over $[0, \lambda_{a_t}/(1 - \lambda_{a_t})]$. The weights and the active set are
updated as in away-step Frank–Wolfe, and an away step with the maximal step size drops $a_t$.
```

```{prf:proposition} Complexity of fractional away-step Frank–Wolfe
:label: prop-frank-wolfe-restarting-complexity
:enumerator: 4.1

Let $f$ be convex and $L$-smooth, let $D$ bound the diameter of $\operatorname{conv}(\mathcal{V})$,
and let $w_0 > 0$ satisfy $e^{-\gamma} w_0/2 \le L D^2$ and $f(x_0) - f^\star \le \mu w_0^r$. If
Algorithm 1 has not stopped before iteration $T$, then

$$
T \le |S_0| - |S_T| + 16 e^{2\gamma} L D^2 \mu\, w_0^{r-2}.
$$
```

Every step that is not a drop step decreases $f$ by at least $e^{-2\gamma} w_0^2/(8 L D^2)$:
smoothness gives this for the step size $e^{-\gamma} w_0/(2 L D^2) \le 1$, and an away step that
stops before its maximal step size minimizes $f$ along the whole ray, by convexity. Drop steps
shrink the active set by one and the other steps grow it by at most one, so
$T \le |S_0| - |S_T| + 2 T_f$ with $T_f$ the number of full steps, and $T_f$ is at most $\mu w_0^r$
divided by the progress per step.

```{prf:proposition} Burn-in phase
:label: prop-frank-wolfe-restarting-burn-in
:enumerator: 4.2

Let $f$ be convex and $L$-smooth with $L > 0$, let $D > 0$ bound the diameter of
$\operatorname{conv}(\mathcal{V})$ and let $\gamma > 0$. Scheduled restarts with $W_0 > 0$ reach the
condition $e^{-\gamma} W_k/2 \le L D^2$ of Proposition 4.1 at some restart
$k \le \lfloor \log(W_0/(2 L D^2))/\gamma \rfloor$, after at most
$|S_0| - |S_{\tau_k}| + 8 e^{\gamma} k$ iterations.
```

While the condition fails, the full steps of a run make progress $e^{-\gamma} W_k/4$ with step size
$1$. The primal gap at the start of the run is at most $W_k$ by Lemma 2.3, so the run takes at most
$8 e^{\gamma}$ steps beyond the change in the size of the active set; and the gap drops by the
factor $e^{-\gamma}$ from one run to the next.

## Scheduled restarts

```{prf:definition} Scheduled restarts (Algorithm 2)
:label: def-frank-wolfe-restarting-restarts
:nonumber:

Scheduled restarts with parameter $\gamma > 0$ run Algorithm 1 repeatedly. Run $k$ starts at
iteration $\tau_k$ from the output of run $k - 1$, with $w_0$ the strong Wolfe gap $W_k$ of its
initial state, and stops at iteration $\tau_{k+1}$, where the strong Wolfe gap $W_{k+1}$ is at most
$e^{-\gamma} W_k$.
```

```{prf:theorem} Rate of scheduled restarts
:label: thm-frank-wolfe-restarting-restarts
:enumerator: 5.1

Let $f$ be convex and $L$-smooth with a $(\theta, c)$-Hölderian error bound on
$\operatorname{conv}(\mathcal{V})$, $\theta \in [0, 1/2]$, let $\delta > 0$ have the scaling
property, let $D$ bound the diameter, let $\gamma > 0$, and assume $e^{-\gamma} W_0/2 \le L D^2$.
With $r = 1/(1-\theta)$, $K = 16 e^{2\gamma} L D^2 (c/\delta)^r$ and
$\tilde{T} = \max\{0, \tau_R - (|S_0| - |S_{\tau_R}|)\}$ after $R$ restarts,

$$
f(x_{\tau_R}) - f^\star \le \frac{W_0}{(1 + \tilde{T} C_\gamma)^{1/(2-r)}},
\qquad C_\gamma = \frac{e^{\gamma(2-r)} - 1}{K W_0^{r-2}},
$$

when $\theta < 1/2$, and $f(x_{\tau_R}) - f^\star \le W_0 e^{-\gamma \tilde{T}/K}$ when
$\theta = 1/2$.
```

Since $1/(2 - r) = (1 - \theta)/(1 - 2\theta)$, this is the rate $O(T^{-(1-\theta)/(1-2\theta)})$
for $\theta < 1/2$: the rate $O(1/T)$ for $\theta = 0$, faster rates in between, and linear
convergence for $\theta = 1/2$. By Lemma 3.6, $f(x_{\tau_k}) - f^\star \le (c/\delta)^r W_k^r$, so
Proposition 4.1 bounds run $k$ by $K W_k^{r-2}$ iterations beyond the change in the size of the
active set. For $\theta = 1/2$ every run costs at most $K$ and the gap drops by $e^{-\gamma}$ per
run. For $\theta < 1/2$ the numbers $u_k = W_k^{r-2}$ grow by at least the factor $e^{\gamma(2-r)}$
per run, so their sum up to $R$ is at most $(u_R - u_0)/(e^{\gamma(2-r)} - 1)$, which gives
$u_R \ge u_0 (1 + \tilde{T} C_\gamma)$.

## Vanilla Frank–Wolfe over strongly convex sets

```{prf:theorem} Strongly convex sets
:label: thm-frank-wolfe-restarting-strongly-convex
:enumerator: 7.3

Let $\mathcal{C}$ be compact and $\alpha$-strongly convex with diameter $D > 0$, and let $f$ be
convex and $L$-smooth with a $(\theta, c)$-Hölderian error bound, $\theta \in (0, 1/2]$. With
$K = (Lc/\alpha)^{1/(1-\theta)}$ and $t_0 = \max\{\lfloor \log_{1/2}(2K/(LD^2)) \rfloor + 2, 1\}$,
every run of Frank–Wolfe with short steps satisfies $f(x_t) - f^\star \le (LD^2/2)\,2^{1-t}$ for
$1 \le t < t_0$ and $f(x_t) - f^\star \le K/(1 + (1 - \theta)(t - t_0)/2)^{1/(1-\theta)}$ for
$t \ge t_0$, the rate $O(t^{-1/(1-\theta)})$.
```

This is the case $q = 2$ of Theorem 2.10 of [Frank–Wolfe over uniformly convex
sets](../frank-wolfe-uniformly-convex-sets/index.md), and the formal proof is that theorem.

:::{note}
**Differences from the paper.**
- The statements hold in real normed spaces.
- Lemmas 2.3 and 3.6 are stated for a given active set $S$ with the gap $w(x, S)$. Since Lemma 3.6
  holds for every active set of $x$, it gives the paper's bound with $w(x) = \min_S w(x, S)$. The
  scaling property is that of the away-step entry, which the pyramidal width satisfies (Lemma 3.4 of
  the paper).
- Algorithms 1 and 2 are stated for $f$ convex and $L$-smooth on the whole space, with $L D^2$ in
  place of the away curvature; exact line search along an away direction uses convexity beyond the
  maximal step size.
- Proposition 4.1 holds for every $w_0 > 0$ with the burn-in condition and a strong Wolfe primal
  bound at $x_0$. Proposition 4.2 bounds the iterations up to the first restart with the burn-in
  condition, by $|S_0| - |S_{\tau_k}| + 8 e^{\gamma} k$.
- In Theorem 5.1 the constant of the strong Wolfe primal bound is $(c/\delta)^r$, by Lemma 3.6; the
  paper writes $\mu = c/\delta$. The proof bounds every run with its own initial gap $W_k$ and
  telescopes $W_k^{r-2}$; the paper bounds $W_k^{r-2}$ by $(W_0 e^{-\gamma k})^{r-2}$, which is not
  justified since $W_k \le W_0 e^{-\gamma k}$ and $r - 2 \le 0$, but the stated rate holds. The
  count $\tilde{T}$ is replaced by $\max\{0, \tilde{T}\}$, because a Frank–Wolfe step with step size
  $1$ resets the active set to a single vertex, so $\tilde{T}$ can be negative.
- Theorem 7.3 is stated with explicit constants; its recursion constant $(\alpha/c)/(2L)$ improves
  the paper's $\alpha/(8Lc)$. The case $\theta = 0$ is the classical rate.
:::

## Coverage

This entry covers Lemmas 2.3 and 3.6, Algorithms 1 and 2 with Propositions 4.1 and 4.2 and Theorem
5.1, and Theorem 7.3; Corollary 5.2 specializes Theorem 5.1 and is not stated separately. Not
covered are the robustness in $\gamma$ (Proposition 5.3), the Hölder smooth versions (Section 6),
the fractional Frank–Wolfe algorithm (Section 7), the one-shot analysis of Appendix A and the
experiments.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWRestart/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-restarting.md
```
