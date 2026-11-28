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
away-step Frank–Wolfe with scheduled restarts (Propositions 4.1, 4.2 and 5.3, Theorem 5.1), its
analysis under Hölder smoothness (Section 6), fractional Frank–Wolfe (Lemma 7.1 and Proposition
7.2), the rate of vanilla Frank–Wolfe over strongly convex sets (Theorem 7.3) and the appendices
(Lemmas A.1 and B.1); numbers refer to the arXiv version.
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

The schedule parameter $\gamma$ enters only through the constant, and $\gamma = 1/2$ is a robust
choice.

```{prf:proposition} Robustness in the schedule parameter
:label: prop-frank-wolfe-restarting-robust
:enumerator: 5.3

Write $C_\gamma = (e^{\gamma(2-r)} - 1)/(e^{2\gamma} K_0 W_0^{r-2})$ for the constant of Theorem
5.1, with $K_0 = 16 L D^2 (c/\delta)^r$. For $r = 1$ and every $\gamma > 0$,

$$
\frac{W_0}{1 + \tilde{T} C_{1/2}} \le \frac{e}{4(\sqrt{e} - 1)} \cdot
\frac{W_0}{1 + \tilde{T} C_\gamma},
$$

and for $r = 2$ the bound $W_0 e^{-\gamma \tilde{T}/(e^{2\gamma} K_0)}$ is smallest at
$\gamma = 1/2$.
```

For $r = 1$, $C_\gamma$ is proportional to $e^{-\gamma} - e^{-2\gamma} \le 1/4$, which is
$e/(4(\sqrt{e} - 1)) \approx 1.05$ times its value at $\gamma = 1/2$; for $r = 2$ the exponent is
proportional to $\gamma e^{-2\gamma}$, which is largest at $\gamma = 1/2$.

## Hölder smoothness

Hölder smoothness interpolates between nonsmooth and smooth objectives. In the analysis it only
enters through the curvature term of a step.

```{prf:definition} Hölder curvature
:label: def-frank-wolfe-restarting-holder
:nonumber:

The function $f$ has Hölder curvature at most $C$ with exponent $s$ over
$\operatorname{conv}(\mathcal{V})$ if
$f(x + \eta(u - v)) \le f(x) + \eta \langle \nabla f(x), u - v \rangle + C \eta^s/s$ for all
$x, u, v \in \operatorname{conv}(\mathcal{V})$ and $\eta \in [0, 1]$. An $(L, s)$-Hölder smooth
function has Hölder curvature at most $L D^s$.
```

```{prf:proposition} Complexity under Hölder smoothness
:label: prop-frank-wolfe-restarting-holder-complexity
:enumerator: 6.1

Let $f$ be convex and differentiable with Hölder curvature at most $C$ and exponent $s > 1$, and let
$w_0 > 0$ satisfy $e^{-\gamma} w_0/2 \le C$ and $f(x_0) - f^\star \le \mu w_0^r$. If Algorithm 1 has
not stopped before iteration $T$, then

$$
T \le |S_0| - |S_T| + 2^{1+\frac{s}{s-1}} \frac{s}{s-1} e^{\frac{s}{s-1}\gamma}
\mu\, C^{\frac{1}{s-1}} w_0^{r - \frac{s}{s-1}}.
$$
```

A full step now decreases $f$ by $\eta G - C\eta^s/s$ with $G = e^{-\gamma} w_0/2$; at
$\eta_0 = (G/C)^{1/(s-1)} \le 1$ this is $(1 - 1/s) G \eta_0$, and the count is as in Proposition
4.1.

```{prf:theorem} Rate of scheduled restarts under Hölder smoothness
:label: thm-frank-wolfe-restarting-holder
:enumerator: 6.2

Let $f$ be as in Proposition 6.1 with a $(\theta, c)$-Hölderian error bound,
$r = 1/(1-\theta) < s/(s-1)$, let $\delta > 0$ have the scaling property, let $\gamma > 0$, and
assume $e^{-\gamma} W_0/2 \le C$. With $\tau = s/(s-1) - r$,
$K = 2^{1+\frac{s}{s-1}} \frac{s}{s-1} (c/\delta)^r C^{\frac{1}{s-1}} e^{\frac{s}{s-1}\gamma}$ and
$\tilde{T} = \max\{0, \tau_R - (|S_0| - |S_{\tau_R}|)\}$,

$$
f(x_{\tau_R}) - f^\star \le \frac{W_0}{(1 + \tilde{T} C_\gamma)^{1/\tau}},
\qquad C_\gamma = \frac{e^{\gamma\tau} - 1}{K W_0^{r - \frac{s}{s-1}}}.
$$
```

The proof is that of Theorem 5.1 with the exponent $2 - r$ replaced by $\tau$: run $k$ costs at most
$K W_k^{-\tau}$ iterations beyond the change in the active set, and $W_k^{-\tau}$ grows by the
factor $e^{\gamma\tau}$ per run.

```{prf:proposition} Burn-in phase under Hölder smoothness
:label: prop-frank-wolfe-restarting-holder-burn-in
:enumerator: 6.3

Let $f$ be as in Proposition 6.1 with $C > 0$ and let $\gamma > 0$. Scheduled restarts with
$W_0 > 0$ reach the condition $e^{-\gamma} W_k/2 \le C$ at some restart
$k \le \lfloor \log(W_0/(2C))/\gamma \rfloor$, after at most
$|S_0| - |S_{\tau_k}| + 4 \frac{s}{s-1} e^{\gamma} k$ iterations.
```

While the condition fails, step size $1$ gives the full steps progress at least $(1 - 1/s) G$.

## Fractional Frank–Wolfe

The same restarts work for vanilla Frank–Wolfe when the minimizers lie in the interior of a general
compact convex set $\mathcal{C}$, with the Frank–Wolfe gap $g(x)$ in place of the strong Wolfe gap.

```{prf:definition} Fractional Frank–Wolfe and its restarts (Algorithms 3 and 2)
:label: def-frank-wolfe-restarting-fractional-fw
:nonumber:

Fractional Frank–Wolfe starts at $x_0 \in \mathcal{C}$ and stops once the Frank–Wolfe gap is at most
$e^{-\gamma} g(x_0)$; otherwise it steps towards a Frank–Wolfe vertex with exact line search over
$[0, 1]$. Scheduled restarts run it repeatedly, run $k$ starting at iteration $\tau_k$ with the gap
$G_k$ there and stopping at $\tau_{k+1}$ with $G_{k+1} \le e^{-\gamma} G_k$.
```

```{prf:lemma} Frank–Wolfe gap near an interior optimum
:label: lem-frank-wolfe-restarting-interior
:enumerator: 7.1

If the closed ball of radius $z > 0$ around $x^\star$ lies in $\mathcal{C}$ and
$\|x - x^\star\| \le z/2$, then $g(x) \ge \frac{z}{2} \|\nabla f(x)\|$.
```

The point $x - \frac{z}{2} u$ lies in the ball for every unit vector $u$, so the Frank–Wolfe vertex
does at least as well as it.

```{prf:proposition} Scheduled restarts of fractional Frank–Wolfe
:label: prop-frank-wolfe-restarting-fractional-fw
:enumerator: 7.2

Let $\mathcal{C}$ be compact and convex with diameter at most $D$, let $f$ be convex and $L$-smooth
with a $(\theta, c)$-Hölderian error bound, $\theta \in [0, 1/2]$, and let the balls of radius
$z > 0$ around the minimizers, within the affine hull of $\mathcal{C}$, lie in $\mathcal{C}$. Let
$\gamma > 0$ and $e^{-\gamma} G_0 \le L D^2$. With $r = 1/(1-\theta)$ and
$K = 2 e^{2\gamma} L D^2 (c/z)^r$, after $T = \tau_R$ iterations

$$
f(x_T) - f^\star \le \frac{G_0}{(1 + T C_\gamma)^{1/(2-r)}},
\qquad C_\gamma = \frac{e^{\gamma(2-r)} - 1}{K G_0^{r-2}},
$$

for $\theta < 1/2$, and $f(x_T) - f^\star \le G_0 e^{-\gamma T/K}$ for $\theta = 1/2$.
```

The balls around the minimizers give $g(x) \ge \frac{z}{c} (f(x) - f^\star)^{1-\theta}$ at every
point of $\mathcal{C}$ (Proposition 5.3 of [Affine-invariant accelerated rates for Frank–Wolfe with
open-loop step-sizes](../frank-wolfe-affine-invariant-open-loop/index.md)), so
$f(x) - f^\star \le (c/z)^r g(x)^r$. Every iteration of a run decreases $f$ by at least
$e^{-2\gamma} G_k^2/(2 L D^2)$, so run $k$ takes at most $K G_k^{r-2}$ iterations, and the restarts
are telescoped as in Theorem 5.1.

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

## The appendices

Run once with a large $\gamma$, fractional away-step Frank–Wolfe is no faster than Frank–Wolfe.

```{prf:lemma} One run with a large schedule parameter
:label: lem-frank-wolfe-restarting-one-shot
:enumerator: A.1

Let $f$ be convex and $L$-smooth and let $D$ bound the diameter of
$\operatorname{conv}(\mathcal{V})$. As long as Algorithm 1 takes Frank–Wolfe steps, that is the
Frank–Wolfe gap exceeds $e^{-\gamma} w_0/2$, its iterates satisfy $f(x_t) - f(y) \le 2 L D^2/t$ for
every $y \in \operatorname{conv}(\mathcal{V})$ and $t \ge 1$.
```

With exact line search and the Frank–Wolfe gap at least the primal gap $h_t$,
$h_{t+1} \le h_t - \eta h_t + \eta^2 L D^2/2$ for every $\eta \in [0, 1]$; $\eta = 1$ gives
$h_1 \le L D^2/2$, and $\eta = h_t/(L D^2)$ gives $h_t \le 2 L D^2/(t + 2)$ by induction. Once
Algorithm 1 takes an away step or stops, the primal gap is at most $e^{-\gamma} w_0$ by Lemma 2.3,
so a single run with $e^{-\gamma} w_0 \lt \varepsilon$ reaches accuracy $\varepsilon$ after
$2 L D^2/\varepsilon$ iterations, but no faster.

```{prf:lemma} A recurrence
:label: lem-frank-wolfe-restarting-recurrence
:enumerator: B.1

Let $h_t \ge 0$ satisfy $h_{t+1} \le h_t \max\{1/2, 1 - M h_t^\beta\}$ with $M > 0$ and
$\beta \in (0, 1]$. If $k \ge 1/(2^\beta - 1)$, $C' \ge 1/(2^\beta - 1)$, $h_0 k^{1/\beta} \le C$
and $2 (C'/M)^{1/\beta} \le C$, then $h_t \le C/(t + k)^{1/\beta}$ for all $t \ge 0$.
```

The induction uses $x = 1/(t + k) \le 2^\beta - 1$, where the chord of the convex map
$y \mapsto y^{1/\beta}$ gives $(1 + x)^{1/\beta} \le 1 + x/(2^\beta - 1) \le 1 + C' x$. If $h_t$ is
at most half the bound, halving suffices; otherwise $M h_t^\beta \ge C' x$, and
$(1 - C'x)(1 + C'x) \le 1$ closes the step.

:::{admonition} Errata
:class: warning
Lemma B.1 assumes only $k \ge (2 - 2^\beta)/(2^\beta - 1) = 1/(2^\beta - 1) - 1$, and its induction
step is carried out for $t \ge 1$, so the step from $t = 0$ to $t = 1$ is missing. It fails for
$\beta = 1$, $M = 1$, $k = 1/100$, $C' = 1$, $C = 2$, $h_0 = 100$ and $h_1 = 50$, which satisfy the
hypotheses ($h_1 \le h_0 \max\{1/2, 1 - 100\}$ and $C \ge \max\{h_0 k, 2 C'/M\}$), while
$h_1 \gt C/(1 + k) \approx 1.98$. The lemma holds with $k \ge 1/(2^\beta - 1)$.
:::

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
  $1$ resets the active set to a single vertex, so $\tilde{T}$ can be negative. Theorem 6.2 is
  treated the same way.
- Proposition 5.3 states the factor $\sqrt{e/(4(\sqrt{e} - 1))}$. Its proof bounds the ratio of the
  two bounds at $r = 1$ by this square root, but there the exponent $1/(2 - r)$ is $1$ and the ratio
  tends to $e/(4(\sqrt{e} - 1))$ as $\tilde{T}$ grows. The entry states the cases $r = 1$, with this
  factor, and $r = 2$; for $1 \lt r \lt 2$ the proof uses that the ratio decreases in $r$, which is
  not shown.
- Section 6 assumes the Hölder curvature bound directly. In Theorem 6.2 the paper writes
  $W_0^{\tau}$ in the denominator of $C_\gamma$; the proof gives $W_0^{r - s/(s-1)} = W_0^{-\tau}$
  there, as stated here.
- Proposition 7.2 bounds the primal gap through balls around the minimizers at every point of
  $\mathcal{C}$, which gives the constant $(c/z)^r$ and needs no second burn-in condition. With its
  Lemma 7.1 the paper's argument gives $(2c/z)^r$; it writes $\mu = (cz/2)^{1/(1-\theta)}$ and
  applies the error bound without $c$. The bound for $\theta = 1/2$ has $2$ where the paper has $8$.
  The restarts are explicit (Algorithm 2 with Algorithm 3 inside) rather than through the parameter
  $\Phi_t$ of Algorithm 4.
- Lemma A.1 is stated as the rate while Frank–Wolfe steps are taken; with Lemma 2.3 it gives the
  paper's statement. Lemma B.1 assumes $C' \ge 1/(2^\beta - 1)$, which the paper's condition
  $C' \ge 1/(\beta - (1 - \beta)(2^\beta - 1))$ implies.
- Theorem 7.3 is stated with explicit constants; its recursion constant $(\alpha/c)/(2L)$ improves
  the paper's $\alpha/(8Lc)$. The case $\theta = 0$ is the classical rate.
:::

## Coverage

This entry covers all results of the paper: Lemmas 2.3 and 3.6, Sections 4 to 7 and the appendices.
Corollary 5.2 specializes Theorem 5.1 and is not stated separately, Proposition 5.3 is stated for
$r = 1$ and $r = 2$, and the experiments are not covered.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWRestart/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-restarting.md
```
