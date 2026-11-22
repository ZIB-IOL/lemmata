---
title: Finite certificates and quantitative bounds
---

## Signed convolution coordinates

For a three-party sign triple let $A,B,C$ be its sign polynomials and write
$ABC=\sum_{r=0}^{m-1}c_r X^r$ modulo $X^m+1$. Write $d=\lceil m/2\rceil$.
Our integer profile is $q=(2c_0,c_1-c_{m-1},\ldots,c_{d-1}-c_{m-d+1})$.
For $d=1$ only $2c_0$ occurs.

```{prf:theorem} Four finite convex-hull identities
:label: thm-symmetric-bell-polytope-followup-small-hulls

Take all triples of sign rows at $m=2,3,4,5$ and apply $q\mapsto M_m q/D_m$.
The convex hull of the resulting points is the standard $\ell^1$ unit ball
in dimensions $1,2,2,3$, respectively. The denominators are $4,144,96,3200$.
The integer matrices, in the same order, are
$$
(1),\quad
\begin{pmatrix}9&9\\3&-5\end{pmatrix},\quad
\begin{pmatrix}3&4\\3&-4\end{pmatrix},\quad
\begin{pmatrix}50&75&25\\50&-25&-75\\12&-26&26\end{pmatrix}.
$$
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-small-hulls)
:nonumber:

Kernel evaluation checks the integer bound $\|M_m q\|_1\le D_m$ for
every triple. Identical products of the first two rows need only be
checked once. Separate sign triples attain each signed coordinate axis.
Convexity and the representation of the $\ell^1$ ball as the hull of
the signed axes give both inclusions.
```

```{prf:theorem} Three strict separating certificates
:label: thm-symmetric-bell-polytope-followup-three-shifts

At $m=17,28,32$, one additional signed input shift in the fundamental
frequency triple gives a profile outside the real convex hull of the signed
canonical frequency profiles. The support bound and the shifted value are
$(7114,7118)$, $(174740,174748)$, and $(39468,39476)$, respectively.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-three-shifts)
:nonumber:

Use the sign $+1$ when $sx\bmod 2m<m$, and $-1$ otherwise, for the
odd frequencies $s=1,3,\ldots,2d-1$. Cube the associated sign row by signed
cyclic convolution, apply its canonical cyclic shift, and fold under reflection.
For a precise convention, put $g=\gcd(m,s)$, $L=m/g$, $u=s/g$, and choose
$k\in[0,2L)$ with $uk+\lfloor3(L-1)/2\rfloor\equiv0\pmod{2L}$.
Folding the antiperiodic cube $c$ gives $q_r=c_{r-k}+c_{-r-k}$. The
shifted test point increases the fundamental $k$ by one.

For example, at $m=17$ an integer normal is $(5,7,9,5,6,0,1,-7,-27)$.
The largest absolute value on the canonical columns is at most 7114 and
the shifted point has value 7118. Lean evaluates the integer inequalities
at all three sizes and applies the same real half-space argument to each.
The theorem proves exclusion from this specified hull. A general conclusion
about affine equivalence to a cross-polytope also requires exposure and a
vertex count. At $m=17$, the needed extreme-point count is
[](#thm-symmetric-bell-cross-polytope-extreme) of @ma2026threeparty.
```


```{prf:theorem} Exact separation on the closed profiles
:label: thm-symmetric-bell-polytope-followup-closed

For every odd $m=17,19,\ldots,91$ and every even $m=28,30,\ldots,90$,
the shifted closed profile lies outside the real convex hull of its signed
canonical closed profiles.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-closed)
:nonumber:

In the folding formula above, replace the raw cube at index $r$ by the
following explicit function. For $g=\gcd(m,s)$, $L=m/g$, $u=s/g$,
$t=ur\bmod L$, take $g^2[2(t+1)(t+2-L)-L]$ with positive sign on the
first half of the $2L$-period of $ur$ and negative sign on the second.
For each of the 70 sizes, the supplied integer normal bounds all signed
columns and gives a strictly larger value at the shifted point. The
kernel evaluates those inequalities and the half-space argument extends
them to the real hull. The all-size theorem is stated for this explicit
quadratic formula. The direct-convolution theorem above checks the raw
definition at three sizes.
```


## An infinite range for the shifted score

Put $x=\pi/(2m)$, $J=\{3,5,7,\ldots,23\}$ and
$R_h=\sin(x)/\sin(hx)$. Define
$$
 W_p=\frac{1+(9/10)\sum_{h\in J}R_h^3\cos(hp)}{\cos p},
 \qquad
 S_p(q)=W_p\cos q-(9/10)\sum_{h\in J}R_h^3\cos(hq).
$$

```{prf:theorem} Strict shift gain for every setting count at least 92
:label: thm-symmetric-bell-polytope-followup-asymptotic

For every integer $m\ge92$ and both $p=0$ and $p=x$,
$S_p(p)=1<S_p(p+2x)$.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-asymptotic)
:nonumber:

Substitute the double- and triple-angle identities into the score difference
for the two possible phases. Factor out $2\sin^2 x$ or $4\sin^2 x$,
respectively. The remaining expression admits strict rational bounds on
$0<x\le171/10000$. The source also bounds the sum of secondary cubic radii
for reduced orders of length at least 16 by $86/1000$. These are
trigonometric inequalities about the displayed scores. Identifying every
strategy in the projected polytope with the requisite Fourier profile is
a further mathematical step.
```


```{prf:theorem} One-party energy in independent odd Fourier modes
:label: thm-symmetric-bell-polytope-followup-energy

Let $m\ge1$ and $a_j\in\{-1,1\}$ for $0\le j<m$. For $0\le k<m$ put
$A_k=\sum_j a_j\exp(\pi i(2k+1)j/m)$,
$g_k=\gcd(2k+1,m)$ and $b_k=\sin(\pi g_k/(2m))|A_k|/g_k$.
Take the smaller index from each conjugate pair $k,m-1-k$, counting the
self-conjugate real mode once when $m$ is odd. Over these representatives,
$\sum_k b_k^2\le5/4$.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-energy)
:nonumber:

Character orthogonality applied to the ordinary Fourier transform of
$a_j\exp(\pi i j/m)$ gives $\sum_k |A_k|^2=m^2$ over the full spectrum.
For a conjugate pair the two moduli are equal and
$\sin(\pi g_k/(2m))/g_k\le\pi/(2m)$. At the self-conjugate mode the
factor is exactly $1/m$. Applying these bounds to the full Parseval sum
and using $\pi^2<10$ gives the stated estimate.
```


## When the signed columns exhaust a hull

```{prf:theorem} Recovery from one-party energy and a coordinate gap
:label: thm-symmetric-bell-polytope-followup-recovery

Let $A\subset\mathbb R^d$, $1\le d\le m$, $m\ge2$. Let $V$ be a square
matrix with unit diagonal and suppose $A$ contains all its signed columns.
Every other $z\in A$ satisfies $|z_i|\le1-m^{-2}$. For every $z\in A$
suppose there are nonnegative amplitudes $a_{pi}$, one per party and mode,
such that $\sum_i a_{pi}^2\le5/4$ for each $p$ and
$|z_i|\le C\prod_{p=1}^N a_{pi}$, with $C\ge0$. If
$C^2(5/8)^N\le 1/(4m^3)$, then $V$ is invertible and
$\operatorname{conv} A=V\{z:\sum_i|z_i|\le1\}$.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-recovery)
:nonumber:

For distinct $i,j$, each product $a_{pi}a_{pj}$ is at most $5/8$.
Consequently $|z_i z_j|\le t=C^2(5/8)^N$. Applying this to the signed
columns bounds every off-diagonal entry of $V$ by $t$. The triangle
inequality gives $\|Vy\|_1\ge(1-mt)\|y\|_1$. For every remaining atom,
the product bound and coordinate gap imply $\|z\|_1+mt<1$.
Invertibility puts these atoms inside the image of the unit ball. The signed
columns give the reverse inclusion after taking convex hulls.
```

The recovery theorem is conditional on the stated data. The full three-party
classification, the equivalence for every party count at seventeen settings,
and the uniform Bell assertion for every setting count are broader statements
than these certificate theorems.
