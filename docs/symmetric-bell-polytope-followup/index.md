---
title: Facet lifting and frequency certificates for symmetric Bell polytopes
---

```{include} ../_generated/provenance/symmetric-bell-polytope-followup.md
```

A facet of the three-party, four-setting symmetry projection lifts to a face strictly
contained in another proper exposed face of the full local polytope. This gives a
counterexample to the facet-lifting observation for odd party count and even
setting count in Section V of the third arXiv version of Designolle, Vértesi and
Pokutta’s paper [@designolle2023symmetric]. The journal article describes the
underlying symmetry projection [@designolle2024symmetric]. Bancal, Gisin and
Pironio had exhibited this phenomenon under exchange of the
two parties in the two-setting probability polytope (Figure 1 and their $(2,2,2)$
example) [@bancal2010looking].

The same section also conjectured that the projected polytope is always a
cross-polytope. The seventeen-setting counterexample for three parties is due
to the Trureturing project [@omega2026symmetric]. Haobo Ma and Wenlin Zhang
adapted its proof for Lemmata [@ma2026threeparty]. Their
[](#thm-symmetric-bell-cross-polytope-extreme) supplies the nineteen extreme
points used in the corollary below.

## Which projection?

Write $P_{N,m}$ for the convex hull of all tensors
$p_{x_1,\ldots,x_N}=\prod_i a_i(x_i)$ with independently chosen
$a_i:\{0,\ldots,m-1\}\to\{-1,1\}$. There are no marginal coordinates.
Extend the input basis by $e_{x+m}=-e_x$. The four generators following Eq. (23) in Section IV of
@designolle2023symmetric are a transposition of the first two
parties, a cycle of the parties, the opposite input shifts $(+1,-1)$ on
the first two parties, and simultaneous input reflection $x_i\mapsto-x_i$.
Reduction of every index includes its antiperiodic sign. Let $H$ be the
common fixed subspace and $\Gamma$ its orthogonal projection. The group
is finite and orthogonal, hence its average equals $\Gamma$. We use
the definitions of these generators, $P_{N,m}$ and $\Gamma$ from the Ma–Zhang
formalization [@ma2026threeparty], and write $K_{N,m}=\Gamma(P_{N,m})$.

## A projected facet whose lift has a larger proper face

Take $(N,m)=(3,4)$. For $s=i+j+k=4q+r$ with $0\le r<4$, let
$$
 U_{ijk}=(-1)^q\mathbf{1}_{r=0},\qquad
 W_{ijk}=(-1)^q(\mathbf{1}_{r=1}-\mathbf{1}_{r=3}).
$$
Set $u(p)=\langle p,U\rangle$, $w(p)=\langle p,W\rangle$.
These unnormalized sums are our two coordinates. The functional $u$ is the
$[1,0,0,0]$ inequality in Section IX.1 of @designolle2023symmetric. Equations
(34)–(35) and Table IV there give its local bound $8$ at $N=3$.

```{prf:theorem} Reconstruction of the Reynolds projection
:label: thm-symmetric-bell-polytope-followup-reconstruction

For every real tensor $p$,
$\Gamma p=u(p)U/16+w(p)W/32$.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-reconstruction)
:nonumber:

The four generators fix $U$ and $W$. Signed generator words take every
one of the 64 indices to $(0,0,r)$ for $r=0,1,2$. At $(0,0,2)$ reflection
reverses the sign, so every fixed tensor vanishes there. The signed words
give $h=h_{000}U+h_{001}W$ for every $h\in H$.
The two basis tensors have disjoint supports and squared norms 16 and 32.
Taking their inner products with $p$ or with $\Gamma p$ gives the same result.
```

```{prf:theorem} A facet that fails to lift
:label: thm-symmetric-bell-polytope-followup

The set $E=\{h\in K_{3,4}:u(h)=8\}$ is a facet of $K_{3,4}$. Its pullback
$\{p\in P_{3,4}:\Gamma p\in E\}$ lies strictly inside a proper exposed face
of $P_{3,4}$. The formal facet criterion is maximality among proper exposed
faces. Every face of a polytope is exposed.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup)
:nonumber:

Decompose $u$ into four relabelled instances of the three-party Mermin
inequality [@mermin1990extreme]. Each form is at most 2 on every
deterministic tensor and therefore on its convex hull. The first form is
$M(p)=p_{000}-p_{022}-p_{202}-p_{220}$.
Two deterministic triples attain $(u,w)=(8,12)$ and $(8,-12)$, and a third
has $u=0$. A supporting line containing the first two points is the line
$u=8$. A linear functional constant on that line and at a point with
$u\ne8$ is constant on the whole plane. This proves maximality of the
projected face. Reconstruction transports the argument to $K_{3,4}$.

Equality $u=8$ forces all four forms to equal 2. Use the all-positive
strings for parties one and two. With the third string $(-,+,-,+)$,
one obtains $M=2$ and $u=0$. With the third string $(+,+,+,+)$ one
obtains $M=-2$. Thus the pullback sits strictly inside $\{M=2\}$, which
is itself strictly inside $P_{3,4}$.
```


```{prf:theorem} Cross-polytopes at two through five settings
:label: thm-symmetric-bell-polytope-followup-small-cross

For $2\le m\le5$, $K_{3,m}$ is affinely equivalent to the standard
cross-polytope of dimension $\lceil m/2\rceil$. The affine map is
defined on the full tensor space, is injective on $K_{3,m}$, and maps
$K_{3,m}$ onto that cross-polytope.
```

```{prf:proof} of [](#thm-symmetric-bell-polytope-followup-small-cross)
:nonumber:

At four settings the chart $(u,w)$ has image $[-8,8]\times[-12,12]$.
The four corners are attained. The bound $|u|\le8$ follows from the
four Mermin forms and central symmetry. For $w$, partition the 32
terms into four blocks. On each deterministic tensor a block has
value $0$ or $\pm4$, and the sign product forces at least one block
to vanish. The map $(u,w)\mapsto(u/16+w/24,u/16-w/24)$ carries the four
corners to the signed coordinate axes. Reconstruction gives injectivity.

At two, three and five settings the signed generator words give a basis for
the fixed space and certify injectivity of the normalized charts in
[](#thm-symmetric-bell-polytope-followup-small-hulls). Expanding the chart
on an arbitrary sign triple gives exactly the integer convolution formula.
These four equivalences confirm the geometry suggested in Section V of
@designolle2023symmetric. Its Table II counts distinct projected strategies,
including points in the interior.
```


## A corollary at seventeen settings

```{prf:corollary} Twenty extreme points
:label: cor-symmetric-bell-polytope-followup-twenty

$K_{3,17}$ has at least twenty distinct extreme points.
```

```{prf:proof} of [](#cor-symmetric-bell-polytope-followup-twenty)
:nonumber:

By [](#thm-symmetric-bell-cross-polytope-extreme) of @ma2026threeparty,
there are nineteen distinct extreme points. Flipping one party's sign reverses a full
correlation tensor and preserves locality. Projection commutes with negation.
The origin is the midpoint of a nonzero antipodal pair and cannot be extreme.
Negation therefore pairs distinct extreme points. A set of nineteen cannot
be closed under this fixed-point-free involution, giving a twentieth.
This lower bound is a corollary of the earlier counterexample.
```

The [certificate proofs](certificates.md) give the finite and asymptotic statements.
The proof `sumFour` in `Chart.lean` specializes the Ma–Zhang
[finite-sum reindexing](https://github.com/ZIB-IOL/lemmata/blob/653d88676a9bcef74db8c5aff23ad37849e1f6e9/lean/Lemmata/SymmetricBellCrossPolytope/Main.lean#L490-L495)
to four settings. The [attribution notice](NOTICE.txt) identifies the upstream
revisions and the adapted code. The entry uses the [Apache 2.0 license](LICENSE.txt).

```{literalinclude} ../../lean/Lemmata/BellFollowup/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/symmetric-bell-polytope-followup.md
```
