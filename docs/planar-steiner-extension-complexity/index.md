---
title: Exact LP extension complexity of planar Steiner tree polytopes
---

```{include} ../_generated/provenance/planar-steiner-extension-complexity.md
```

The convex hull of the inclusion-minimal Steiner trees of a simple planar graph has worst-case
linear extension complexity $2^{\Theta(\sqrt n)}$, where $n$ is the number of vertices. Two
cofacial terminals already suffice, and the same bound holds for three related
terminal-connectivity polyhedra. The lower bound comes from a face of a planar Hamiltonian path
polytope. It starts from the correlation polytope of a square grid, encodes vertex covers in a
plane graph, and makes every cover the shore of a bond whose dual cycle visits every vertex. A
sphere-cut dynamic program gives the matching upper bound.

```{mermaid}
flowchart LR
  A["COR(L_h), h x h grid"] -->|"cover graph"| B["minimum-cover face of VC(J)"]
  B -->|"Steiner faces"| C["P_min, P_conn, P_up, D on (H, R)"]
  B -->|"face"| D["VC(J)"]
  D -->|"Hamiltonian path face"| E["HP(G', s, t)"]
  E -->|"Feldmann-Rai, Lemma 9"| F["P_min(G', {s, t})"]
  C -->|"pendant transfer"| G["P_conn with two terminals"]
```

Each arrow says that the extension complexity of its source is at most that of its target, by
[](#lem-planar-steiner-extension-complexity-cover),
[](#prop-planar-steiner-extension-complexity-steiner), passing to a face,
[](#thm-planar-steiner-extension-complexity-hp),
[](#lem-planar-steiner-extension-complexity-feldmann) and
[](#lem-planar-steiner-extension-complexity-pendant).

**What Lean checks.** The whole reduction chain above is formalized on explicit graphs: the cover
graph $J$ of the grid, the radial graph $H$ and the flag graph $\Gamma$ with $G'=\Gamma-st$. That
includes the planarity of all three, as face systems that satisfy Euler's formula, and their exact
vertex counts. The resulting lower bounds
[](#thm-planar-steiner-extension-complexity) and [](#thm-planar-steiner-extension-complexity-four)
are proved from one explicit hypothesis, the exponential lower bound for grid correlation
polytopes of @aboulker2019extension, which is not formalized. Also not formalized are the upper
bound ([](#prop-planar-steiner-extension-complexity-upper)), the identity
$P_{\uparrow}=D\cap[0,1]^E$, the terminal-parameter theorem
([](#thm-planar-steiner-extension-complexity-param)) and the remarks on special cases and facets.
Each is marked where it appears.

## The four objects and their bounds

Let $G=(V,E)$ be a finite connected simple graph with $n=|V|$, $m=|E|$, and a terminal set
$T\subseteq V$ with $k=|T|\ge2$. Write $\chi^F$ for the incidence vector of $F\subseteq E$ and
$x(B)=\sum_{e\in B}x_e$. The *support graph* of $F$ has edge set $F$ and the endpoints of these
edges as vertices.

* $P_{\min}(G,T)$ is the convex hull of the $\chi^F$ for the inclusion-minimal edge sets $F$
  connecting $T$. These are exactly the trees spanning $T$ all of whose leaves belong to $T$.
* $P_{\mathrm{conn}}(G,T)$ is the hull for the edge sets whose support graph is connected and
  contains $T$. Nonterminal leaves and cycles are allowed.
* $P_{\uparrow}(G,T)$ is the hull for the edge sets with all of $T$ in one component of $(V,F)$.
  Selected edges may also lie in other components.
* $D(G,T)=P_{\min}(G,T)+\mathbb R^{E}_{\ge0}$ is the Steiner tree dominant.

```{prf:definition} Extension complexity
:label: def-planar-steiner-extension-complexity-xc

An *LP extension* of $P\subseteq\mathbb R^d$ with $m$ inequalities is a polyhedron
$Q=\{y\in\mathbb R^{e}: Ay=b,\ Cy\le f\}$, where $C$ has $m$ rows, together with an affine map
$\pi$ with $\pi(Q)=P$. The extension complexity $\operatorname{xc}(P)\in\mathbb N\cup\{\infty\}$
is the least $m$ over all LP extensions of $P$. Equations are free, coefficients are arbitrary
reals, and there is no symmetry or uniformity requirement.
```

Passing to a face (in Lean: intersecting with a supporting hyperplane, or with any hyperplane)
and taking an affine image can only decrease $\operatorname{xc}$. These are the only operations
the reductions below use.

```{prf:definition} Planar graph (face systems)
:label: def-planar-steiner-extension-complexity-planar

A *planar face system* of a finite simple graph $G$ is a finite family of nonempty edge sets
of $G$, the *faces*, such that

1. every face is an even subgraph in which every vertex has degree $0$ or $2$;
2. every edge of $G$ lies on exactly two faces;
3. $G$ is connected, and the faces are connected through shared edges;
4. Euler's formula holds: $|V|+\#\text{faces}=|E|+2$.

$G$ is *planar* if it has a planar face system.
```

Mathlib has no notion of planarity, so the formalization uses this one. It records exactly what
the proofs use. The facial cycles of a 2-connected plane graph form a planar face system
[@diestel2017graph, Section 4.2]. The notion is more restrictive than planarity, since a bridge
lies on no cycle and hence on no face, but it is sound: a graph with a planar face system is
planar. Indeed, every face lies in the cycle space over $\mathbb Z/2$, because all its degrees are
even. Since every edge lies on exactly two faces, a set of faces sums to zero exactly when it
contains, with each face, the other face at each of its edges; since the faces are connected
through shared edges, only the empty set and the set of all faces do. The faces thus span a space
of dimension $\#\text{faces}-1=|E|-|V|+1$, by Euler's formula, which is the dimension of the cycle
space of the connected graph $G$. Dropping one face therefore leaves a basis of the cycle space in
which every edge lies in at most two members, and $G$ is planar by MacLane's criterion
[@diestel2017graph, Theorem 4.5.1]. Every graph constructed below is shown to be planar in this
sense, with an explicit face system.

```{prf:theorem} Exact extension complexity
:label: thm-planar-steiner-extension-complexity-main

For each of the four objects, the maximum extension complexity over planar instances with at
most $n$ vertices is $2^{\Theta(\sqrt n)}$. For $P_{\min}$ this holds already with two cofacial
terminals on graphs of maximum degree three. The Hamiltonian path polytope with those prescribed
endpoints also attains the lower bound.
```

The lower bounds are the Lean-checked theorems
[](#thm-planar-steiner-extension-complexity) and [](#thm-planar-steiner-extension-complexity-four),
given the grid correlation bound [](#eq-planar-steiner-extension-complexity-grid). The upper
bound is [](#prop-planar-steiner-extension-complexity-upper) (not formalized).

```{prf:theorem} Lower bound with two cofacial terminals
:label: thm-planar-steiner-extension-complexity

Let $c>0$, and suppose that $\operatorname{xc}(\operatorname{COR}(L_h))\ge 2^{ch}$ for every
$h\ge2$, where $L_h$ is the $h\times h$ grid. Then for every $h\ge2$ there are a planar graph
$\Gamma$ on $n=832\,h(h-1)$ vertices and an edge $st$ of $\Gamma$ such that
$$
\operatorname{xc}\bigl(P_{\min}(\Gamma-st,\{s,t\})\bigr)\ \ge\ 2^{(c/29)\sqrt n}.
$$
The terminals $s,t$ are cofacial in $\Gamma-st$, because restoring the edge $st$ keeps the graph
planar.
```

```{prf:theorem} Lower bound for the four polyhedra
:label: thm-planar-steiner-extension-complexity-four

Under the same hypothesis, for every $h\ge2$ there are a planar graph $H$ on
$n=104\,h(h-1)+2$ vertices and a terminal set $R$ such that each of $P_{\min}(H,R)$,
$P_{\mathrm{conn}}(H,R)$, $P_{\uparrow}(H,R)$ and $D(H,R)$ has extension complexity at least
$2^{(c/11)\sqrt n}$.
```

The proofs are at the end, after the reductions
[](#thm-planar-steiner-extension-complexity-reduction) and
[](#thm-planar-steiner-extension-complexity-reduction-four). The table summarizes the bounds. The
two-terminal bounds $O(m)$ for $P_{\uparrow}$ and $D$ come from the flow formulation discussed
before [](#thm-planar-steiner-extension-complexity-param) and are not formalized.

| Object | Unrestricted terminals | Two terminals |
|---|---|---|
| Inclusion-minimal trees $P_{\min}$ | $2^{\Theta(\sqrt n)}$ | $2^{\Theta(\sqrt n)}$ |
| Connected supports $P_{\mathrm{conn}}$ | $2^{\Theta(\sqrt n)}$ | $2^{\Theta(\sqrt n)}$ |
| Terminal-connecting supersets $P_{\uparrow}$ | $2^{\Theta(\sqrt n)}$ | $O(m)$ |
| Dominant $D$ | $2^{\Theta(\sqrt n)}$ | $O(m)$ |

For connected simple planar graphs, $n-1\le m\le3n-6$ when $n\ge3$, so the square-root exponent
can equally be expressed in terms of $m$.

*Not formalized.* The upper bounds use the identity $P_{\uparrow}=D\cap[0,1]^E$. For the
nontrivial inclusion, let $x$ belong to the right-hand side and choose $p\in P_{\min}$ with
$p\le x$. Draw a random minimal tree with marginals $p$. For each absent edge $e$ with $p_e<1$,
add it with probability $(x_e-p_e)/(1-p_e)$. The result connects all terminals and has marginals
$x$. The other inclusion follows by pruning a feasible set to a minimal tree and taking convex
hulls.

## Two-terminal faces

Let $\operatorname{HP}(G,s,t)$ be the convex hull of the Hamiltonian $s$-$t$ paths of $G$. With
two terminals, the minimal trees are precisely the simple $s$-$t$ paths.

```{prf:lemma} Feldmann and Rai, Lemma 9
:label: lem-planar-steiner-extension-complexity-feldmann

For every finite simple graph $G$ on $n$ vertices and all vertices $s,t$,
$$
\operatorname{HP}(G,s,t)=P_{\min}(G,\{s,t\})\cap\{x: x(E)=n-1\}.
$$
In particular $\operatorname{xc}(\operatorname{HP}(G,s,t))\le\operatorname{xc}(P_{\min}(G,\{s,t\}))$.
```

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-feldmann)
:nonumber:

This is Lemma 9 of @feldmann2021extended. A minimal connector of $\{s,t\}$ is an $s$-$t$ path, so
it has at most $n-1$ edges, with equality exactly for Hamiltonian paths. Hence $x(E)\le n-1$ is
valid for $P_{\min}(G,\{s,t\})$, and its face is the hull of the vertices on the hyperplane, the
Hamiltonian $s$-$t$ paths. If there are none, both sides are empty.
```

The identity keeps the graph, its embedding and the two endpoints. Feldmann and Rai's Theorem 1
obtains $2^{\Omega(n)}$ for a family of general graphs from Hamiltonian paths in $K_n-st$ and the
lower bound for the Hamiltonian cycle polytope of complete graphs [@rothvoss2013matching]. That
family is nonplanar for large $n$. The next sections construct a planar family to which the
identity applies.

## A planar source of hard vertex covers

For a graph $L$, let $\operatorname{COR}(L)$ be the convex hull of the vectors
$(x_v,\ x_ux_v)_{v\in V(L),\,uv\in E(L)}$ for $x\in\{0,1\}^{V(L)}$: one binary coordinate per
vertex and one product coordinate per edge. For the $h\times h$ grid $L_h$,

$$
\operatorname{xc}(\operatorname{COR}(L_h))\ \ge\ 2^{\Omega(h)}
$$ (eq-planar-steiner-extension-complexity-grid)

by [@aboulker2019extension, Theorem 3]. This is the external input: Lean takes it as the hypothesis
of [](#thm-planar-steiner-extension-complexity) and [](#thm-planar-steiner-extension-complexity-four).

**The cover graph.** Give every edge $uv$ of $L$ an orientation and a new Boolean variable $z$.
The clauses
$$
A=(\neg x_u\lor\neg x_v\lor z),\qquad B=(x_u\lor\neg z),\qquad C=(x_v\lor\neg z)
$$
enforce $z=x_ux_v$. Their variable–clause incidence graph is the cycle
$x_u,A,x_v,C,z,B,x_u$ with the chord $Az$ ([](#fig-planar-steiner-extension-complexity-gadget)).
For a variable with $d$ literal occurrences, fix a cyclic order of the occurrences and draw a
cycle $\mathsf T_1,\mathsf F_1,\ldots,\mathsf T_d,\mathsf F_d$ of *ports*, one true port
$\mathsf T_i$ and one false port $\mathsf F_i$ per occurrence. Here $d\ge2$. Replace every clause by
a clique on the literal vertices of its two or three occurrences, and join every literal vertex to
the port of its occurrence that represents the falsifying assignment: $\mathsf F_i$ for a positive
literal and $\mathsf T_i$ for a negative one. Call the result the *cover graph* $J$. For the grid
it is drawn in the plane by replacing every variable of the plane incidence graph
([](#fig-planar-steiner-extension-complexity-grid)) by its port cycle, in the planar cyclic order
of its occurrences. Write $F_J$ for the face of $\operatorname{VC}(J)$, the convex hull of the
vertex covers of $J$, spanned by the minimum covers.

```{figure} ./images/gadget.svg
:name: fig-planar-steiner-extension-complexity-gadget
:alt: A hexagon x_u, A, x_v, C, z, B with the chord from A to z. The chord splits the inside into the gadget faces g1 and g2. The clause A lies on the left of the oriented edge uv, and z, B, C on its right.
:width: 55%

The three-clause product gadget. The old variables $x_u,x_v$ are boundary ports, so each gadget
can replace a grid edge independently. The chord $Az$ splits the inside into the two gadget faces
$g_1,g_2$ used in the face system of [](#lem-planar-steiner-extension-complexity-grid-planar).
```

[Open the full-size SVG](./images/gadget.svg).

```{prf:lemma} The cover graph
:label: lem-planar-steiner-extension-complexity-cover

Let $L$ be a finite graph without isolated vertices whose edges are oriented, and fix any cyclic
order of the occurrences of every variable of the product formula above. Then
$\operatorname{COR}(L)$ is an affine image of the minimum-cover face $F_J$ of the cover graph $J$.
In particular $\operatorname{xc}(\operatorname{COR}(L))\le\operatorname{xc}(F_J)$.
```

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-cover)
:nonumber:

An independent set of $J$ has at most $\sum d+\#\{\text{clauses}\}$ vertices: at most $d$ on the
port cycle of a variable with $d$ occurrences and at most one in every clause clique. An
independent set attaining the bound takes one of the two alternating patterns on every cycle,
which defines an assignment, and one vertex of every clique. The chosen literal vertex is not
adjacent to its chosen falsifying port, so it certifies a true literal of its clause. Conversely,
every satisfying assignment attains the bound by choosing a true literal in each clause.
Complementing, the minimum covers of $J$ are the complements of these maximum independent sets;
they correspond to the satisfying assignments together with a choice of true literal per clause.
A variable is true exactly when its true ports are not in the cover. Since the formula forces
$z=x_ux_v$, reading $1-y$ at one true port per variable maps every minimum cover to the point
$(x_v,x_ux_v)$ of its assignment, and every vertex of $\operatorname{COR}(L)$ arises. This affine
map sends $F_J$ onto $\operatorname{COR}(L)$. Here $F_J$ is the face of $\operatorname{VC}(J)$ cut
out by $y(V(J))\ge\tau$, where $\tau$ is the minimum cover size.
```

The general lemma needs no planarity. Planarity comes from the choice of cyclic order, and Lean
verifies it for the grid.

```{prf:lemma} The cover graph of the grid is planar
:label: lem-planar-steiner-extension-complexity-grid-planar

For $h\ge2$, orient the edges of $L_h$ rightward and upward and order the occurrences of every
variable counterclockwise. The cover graph $J$ is then planar, connected and of maximum degree
three, with no isolated vertices. It has $|V(J)|=42h(h-1)$ vertices, $|E(J)|=52h(h-1)$ edges and
$h^2+8h(h-1)+(h-1)^2+1$ faces.
```

```{figure} ./images/grid-incidence.svg
:name: fig-planar-steiner-extension-complexity-grid
:alt: The four grid points of the 2 by 2 grid at the corners of a square, each pair of neighbours joined by a product gadget with its clause A on the left of the edge, oriented rightward or upward, and z, B, C on its right. The gadgets bound an inner cell face and the outer face.
:width: 70%

The plane variable–clause incidence graph of $L_2$. Replacing every variable by its port cycle
and every clause by a clique gives the cover graph $J$.
```

[Open the full-size SVG](./images/grid-incidence.svg).

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-grid-planar)
:nonumber:

An oriented grid edge $e$ contributes seven occurrences $(e,0),\ldots,(e,6)$: $\neg x_u,\neg x_v,z$
in $A$, then $x_u,\neg z$ in $B$ and $x_v,\neg z$ in $C$. Around a grid point $p$, the gadget of the
edge in direction $d\in\{E,N,W,S\}$ contributes two consecutive occurrences of $x_p$, in two
*slots* $(d,0),(d,1)$. The cyclic order runs through the slots counterclockwise and skips the
directions that are absent at the boundary. The occurrences of $z_e$ are ordered $C,A,B$. The
faces of $J$ are:

* one face inside every port cycle;
* one triangle inside every clique of a clause $A$;
* two faces $g_1,g_2$ inside every gadget;
* one face per unit square of the grid;
* the outer face.

Every occurrence $o$ has a region *after* it and a region *before* it, counterclockwise around its
variable. The key identity is that the region after $o$ is the region before the next occurrence.
Within a gadget it is a table lookup. Between consecutive directions at $p$ the region is the
quadrant between them, and a skipped direction only occurs where both quadrants are the outer
face. Each edge of $J$ is assigned the two regions on its sides:

* the cycle edge $\mathsf F_o\mathsf T_{\mathrm{next}(o)}$ separates the variable face from the
  region after $o$;
* the pair edge $\mathsf T_o\mathsf F_o$ separates the variable face from the region on the side of
  the literal vertex;
* the port edge of a literal vertex separates the regions after and before $o$;
* the clique edges separate the triangle from the gadget regions.

At every vertex the incident edges and their face pairs form one of two patterns. Either there are
three edges with face pairs $\{x,y\},\{x,z\},\{y,z\}$, or two edges with the same pair $\{x,y\}$.
In both, every face meets the vertex in $0$ or $2$ of its edges. Every edge has two distinct faces.
$J$ is connected because the grid is, and so is the dual: every face reaches the variable face of
a grid point, and the gadget faces $g_1,g_2$ link the variable faces of neighbouring grid points.
With $E=2h(h-1)$ grid edges, a handshake count gives $|E(J)|=26E$, so Euler's formula reads
$21E+\bigl(h^2+4E+(h-1)^2+1\bigr)=26E+2$, which holds because $E=2h(h-1)$. All finite case
distinctions over the sixteen presence patterns of directions are checked by the Lean kernel.
```

@avis2015extension previously obtained a superpolynomial lower bound for stable-set polytopes of
cubic planar graphs by a different planarization. [](#lem-planar-steiner-extension-complexity-cover)
uses the grid-product coordinates to keep the size quadratic in the exponent parameter $h$.

## The cover face in a planar Steiner instance

Embed $J$ in the sphere. Its vertices will be the *optional* vertices of a new graph $H$.
Subdivide every edge $uv\in E(J)$ by an *edge terminal* $q_{uv}$, put a *face terminal* $f_\varphi$
in every face $\varphi$ of $J$, and join $f_\varphi$ to every vertex on the boundary of $\varphi$.
Write $R$ for the set of all terminals. The graph $H$ is simple, and planar: its faces are the
quadrilaterals $u\,q_{uv}\,v\,f_\varphi$, one for each side $(\varphi,uv)$ of an edge of $J$. If $J$
has $g$ edges, Euler's formula gives $|V(H)|=|V(J)|+g+\#\text{faces}(J)=2g+2$ and $|E(H)|=4g$.

```{figure} ./images/radial.svg
:name: fig-planar-steiner-extension-complexity-radial
:alt: J has vertices a, b, c, d, the sides of a square and the chord ac. Black squares subdivide the edges of J and grey diamonds mark the three face terminals, each joined to the vertices of its face. For the cover S consisting of a and c, the thick blue edges show the connected graph H restricted to the terminals and S; the vertices b and d are grey.
:width: 60%

The radial graph $H$ of a small plane graph $J$. For the cover $S=\{a,c\}$ the thick edges span
$H[R\cup S]$, which is connected.
```

[Open the full-size SVG](./images/radial.svg).

```{prf:lemma} Covers and connectivity
:label: lem-planar-steiner-extension-complexity-radial

Let $J$ be nonempty, without isolated vertices, with a planar face system. If $S\subseteq V(J)$ is
a vertex cover of $J$, then $H[R\cup S]$ is connected.
```

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-radial)
:nonumber:

If $S$ covers $J$, the face terminals on the two sides of an edge $uv$ communicate through a
selected endpoint. The dual of $J$ is connected, so all face terminals communicate, and the edge
terminals and the vertices of $S$ attach.
```

Conversely, the optional vertices in the terminal component of any edge set connecting $R$ form a
vertex cover, because a connected support containing $R$ has to attach $q_{uv}$ through $u$ or $v$.
Lean proves this direction inside the proof of
[](#prop-planar-steiner-extension-complexity-steiner).

```{prf:lemma} The radial graph is planar
:label: lem-planar-steiner-extension-complexity-radial-planar

Let $J$ be nonempty, without isolated vertices, with a planar face system whose links are connected:
the faces around every vertex are connected through faces sharing an edge at that vertex, which
holds automatically for maximum degree three. Then $H$ is planar; its faces are the quadrilaterals
$u\,q_{uv}\,v\,f_\varphi$.
```

```{prf:proposition} Steiner faces
:label: prop-planar-steiner-extension-complexity-steiner

Let $J$ be nonempty, without isolated vertices, with a planar face system. Then
$\operatorname{xc}(F_J)$ is at most the extension complexity of each of $P_{\min}(H,R)$,
$P_{\mathrm{conn}}(H,R)$, $P_{\uparrow}(H,R)$ and $D(H,R)$: each has a face that projects onto the
minimum-cover face $F_J$.
```

```{prf:proof} of [](#prop-planar-steiner-extension-complexity-steiner)
:nonumber:

Let $\tau$ be the minimum cover size and minimize $x(E(H))$. An edge set connecting $R$ whose
terminal component contains $s$ optional vertices has at least $|R|-1+s$ edges, and $s\ge\tau$ because these optional vertices form a cover (the converse noted after
[](#lem-planar-steiner-extension-complexity-radial)). For a minimum cover $S$, take a spanning tree
of $H[R\cup S]$ ([](#lem-planar-steiner-extension-complexity-radial)). All its leaves are
terminals: if an optional $v\in S$ were a leaf, then $H[R\cup(S\setminus v)]$ would be connected,
so $S\setminus v$ would be a cover, again by the converse. Hence the tree is an inclusion-minimal
Steiner tree with $|R|-1+\tau$ edges. Every feasible edge set contains a minimal tree, and all edge
costs are positive, so the four minimum faces coincide, also for the unbounded dominant.

Mark one edge from every optional vertex $v$ to an incident face terminal $f_{\varphi(v)}$. On the
minimum face, maximize the number of marked edges. A tree of the minimum face uses $\tau$ optional
vertices and so has at most $\tau$ markers. For a minimum cover $S$, the markers at $S$ form a forest
in which every optional vertex has degree one; extending it to a spanning tree of $H[R\cup S]$
attains $\tau$ markers. Conversely, a tree attaining both optima uses the marker at every optional
vertex it visits. On this second face, the marker coordinates are exactly the convex hull of the
minimum covers.
```

Together with [](#lem-planar-steiner-extension-complexity-cover) this proves the lower bounds with
unrestricted terminals.

## A hard planar Hamiltonian path face

Draw the barycentric subdivision $Q$ of $H$ in the sphere. Besides the vertices of $H$, it has a
midpoint $z_a$ for every edge $a$ of $H$ and a centre $b_\psi$ for every face $\psi$ of $H$, and it
joins incident objects of different types. Its faces are the triangles $(v,z_a,b_\psi)$ with
$v\in a\subseteq\partial\psi$, the *flags*. The dual of $Q$ is the *flag graph* $\Gamma$, with one
vertex per flag. Two flags are adjacent when they differ in exactly one of the three components.
$\Gamma$ is simple and cubic. Each edge of $H$ has two ends and two sides, so $\Gamma$ has
$4|E(H)|=16|E(J)|$ vertices.

```{prf:lemma} The flag graph is planar
:label: lem-planar-steiner-extension-complexity-flag-planar

Let $(\Phi;Q_0,Q_1,Q_2)$ be a flag system: flags $\Phi$ with components in $Q_0,Q_1,Q_2$ and
fixed-point-free involutions $\tau_0,\tau_1,\tau_2$, where $\tau_i$ changes exactly the
$Q_i$-component. If its flag graph $\Gamma$ is connected and
$2(|Q_0|+|Q_1|+|Q_2|)=|\Phi|+4$, then $\Gamma$ is planar; its faces are the stars of the elements of
$Q_0\cup Q_1\cup Q_2$.
```

```{prf:lemma} Bond–cycle duality
:label: lem-planar-steiner-extension-complexity-duality

Under the same hypotheses, every even edge set of $\Gamma$ (every flag meets an even number of its
edges) is the cut of a 2-colouring of $Q_0\cup Q_1\cup Q_2$, that is, of the vertices of $Q$.
```

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-duality)
:nonumber:

This is the classical duality between cycles of a plane graph and bonds of its dual
[@diestel2017graph, Section 4.6]. The formal proof is linear algebra over $\mathbb Z/2$. Cuts are
even, since every flag meets the cut of a colouring in an even number of edges. The kernel of the
cut map consists of the constant colourings, because $Q$ is connected. Rank–nullity then gives
dimension $|Q_0|+|Q_1|+|Q_2|-1$ for the cut space and dimension $|E(\Gamma)|-|\Phi|+1$ for the
even edge sets. These agree by Euler's relation, since $|E(\Gamma)|=3|\Phi|/2$.
```

```{prf:theorem} A Hamiltonian path face
:label: thm-planar-steiner-extension-complexity-hp

Let $J$ be nonempty, without isolated vertices, with a planar face system whose links are
connected, and let $\Gamma$ be the flag graph of its radial graph $H$. Call an edge of $\Gamma$
*forced* if its dual edge in $Q$ is a spoke $r\,b_\psi$ from a terminal $r\in R$. There is a forced
edge $st$ such that, with $G'=\Gamma-st$, the coordinate projection that reads one designated edge
per optional vertex maps the face of $\operatorname{HP}(G',s,t)$ on which all forced coordinates
equal one onto $\operatorname{VC}(J)$.
```

```{prf:proof} of [](#thm-planar-steiner-extension-complexity-hp)
:nonumber:

A bond is a cut whose two shores are nonempty and connected. By
[](#lem-planar-steiner-extension-complexity-duality), the edge set of a Hamiltonian cycle of
$\Gamma$ is the cut of a colouring of $Q$, and since the cycle is a minimal even set the colouring
has connected monochromatic shores.

*Decoding a cycle.* Take a Hamiltonian cycle containing all forced edges. Up to exchanging the two
colours, all $r\in R$ are red and all centres $b_\psi$ are blue. The bipartite incidence graph
between $R$ and the faces of $H$ is connected, since adjacent faces share a terminal endpoint of
their common edge, and every forced edge joins opposite colours. In the connected red shore, a path
from $q_{uv}$ to another terminal must start through one of the two midpoints of the edges of $H$ at
$q_{uv}$. From that midpoint its next red vertex can only be $u$ or $v$, because the centres are
blue. So the set $S$ of red optional vertices covers $J$. For every optional $v$ fix an incident face
$\varphi(v)$ of $H$. The dual coordinate of $v\,b_{\varphi(v)}$ is $1$ exactly when $v\in S$. This is
a coordinate projection independent of the cycle.

*Lifting a cover.* Fix a cover $S$ and a spanning tree $K$ of $H[R\cup S]$
([](#lem-planar-steiner-extension-complexity-radial)). Colour the old vertices in $R\cup S$ red and
the other old vertices blue, all centres blue, and the midpoint $z_a$ red exactly when $a\in K$ or
$a$ has a blue optional endpoint. The subdivided tree $K$ connects $R\cup S$, and every further red
midpoint attaches to a red terminal at its other end, so the red shore is connected. The dual edges
of $H$ complementary to $K$ connect all faces of $H$: extend the forest $K$ to a spanning tree and
use the complementary dual spanning tree. This is formalized directly, by showing that the faces
stay connected when the edges of a forest are removed. To travel in blue between the centres of
faces adjacent across $a\notin K$, use $z_a$ if it is blue, and otherwise a blue optional endpoint of
$a$, which is adjacent to both centres in $Q$. Every blue midpoint and every blue old vertex attaches
to a centre, so the blue shore is connected. Every flag triangle is bichromatic: its centre is blue,
and if its old vertex $v$ is blue, the midpoint is red by the colouring rule. So the cut meets every
flag in exactly two edges and is a connected 2-regular spanning subgraph of $\Gamma$, a Hamiltonian
cycle. It satisfies the forced coordinates and decodes to $S$.

Finally, delete the forced edge $st$. Restoring it gives a bijection between Hamiltonian $s$-$t$
paths of $G'$ and Hamiltonian cycles of $\Gamma$ through $st$, and on incidence vectors it only
restores a coordinate equal to one. The remaining forced coordinates cut out the face of
$\operatorname{HP}(G',s,t)$ in the statement. The endpoints are cofacial in $G'$ because $\Gamma$ is
planar and contains $st$.
```

The graph $G'$ is subcubic, because $\Gamma$ is cubic, and $s,t$ are cofacial in $G'$, because
$\Gamma$ is planar and contains $st$
([](#lem-planar-steiner-extension-complexity-flag-planar)).

For the grid, combining [](#lem-planar-steiner-extension-complexity-feldmann) with
[](#thm-planar-steiner-extension-complexity-hp) gives graphs on $N=16|E(J)|=O(h^2)$ vertices with
$$
\operatorname{xc}(P_{\min}(G',\{s,t\}))\ \ge\ \operatorname{xc}(\operatorname{HP}(G',s,t))\
\ge\ \operatorname{xc}(\operatorname{VC}(J))\ \ge\ 2^{\Omega(h)}.
$$

## Two terminals for connected supports

```{prf:lemma} Pendant transfer
:label: lem-planar-steiner-extension-complexity-pendant

Let $G$ be a finite graph, $R$ a terminal set and $t_1\ne t_2$ two terminals. Attach a new pendant
vertex to every terminal, and call the result $G^{+}$. Then
$\operatorname{xc}(P_{\mathrm{conn}}(G,R))\le\operatorname{xc}(P_{\mathrm{conn}}(G^{+},\{t_1,t_2\}))$.
```

```{prf:proof} of [](#lem-planar-steiner-extension-complexity-pendant)
:nonumber:

Set all pendant coordinates to one; this is a face. A connected support containing $t_1,t_2$ and all
pendant edges contains every terminal, so deleting the pendant edges maps the face onto
$P_{\mathrm{conn}}(G,R)$. The same proof works for the bounded hull of all terminal-spanning trees
that permit nonterminal leaves.
```

Applied to $(H,R)$ this gives the two-terminal bound for $P_{\mathrm{conn}}$, with linear growth in
the graph size. Attaching pendant vertices keeps $H$ planar, but pendant edges are bridges, so
$H^{+}$ has no planar face system in the sense of
[](#def-planar-steiner-extension-complexity-planar), which needs two faces at every edge. Its
planarity is therefore not part of the formalization.

## The reductions and the lower bounds

```{prf:theorem} Two cofacial terminals
:label: thm-planar-steiner-extension-complexity-reduction

For every $h\ge2$ there are a planar graph $\Gamma$ on $832\,h(h-1)$ vertices and an edge $st$ of
$\Gamma$ with
$\operatorname{xc}(\operatorname{COR}(L_h))\le\operatorname{xc}(P_{\min}(\Gamma-st,\{s,t\}))$.
```

```{prf:theorem} Four polyhedra
:label: thm-planar-steiner-extension-complexity-reduction-four

For every $h\ge2$ there are a planar graph $H$ on $104\,h(h-1)+2$ vertices and a terminal set $R$
such that $\operatorname{xc}(\operatorname{COR}(L_h))$ is at most the extension complexity of each of
$P_{\min}(H,R)$, $P_{\mathrm{conn}}(H,R)$, $P_{\uparrow}(H,R)$ and $D(H,R)$.
```

```{prf:proof} of [](#thm-planar-steiner-extension-complexity-reduction) and [](#thm-planar-steiner-extension-complexity-reduction-four)
:nonumber:

Take the planar cover graph $J$ of the grid
([](#lem-planar-steiner-extension-complexity-grid-planar)). It has maximum degree three, so its links
are connected. By [](#lem-planar-steiner-extension-complexity-cover),
$\operatorname{xc}(\operatorname{COR}(L_h))\le\operatorname{xc}(F_J)$, and
$\operatorname{xc}(F_J)\le\operatorname{xc}(\operatorname{VC}(J))$ since $F_J$ is a face.

For two terminals, let $\Gamma$ be the flag graph. It is connected and satisfies Euler's relation,
so it is planar by [](#lem-planar-steiner-extension-complexity-flag-planar). By
[](#thm-planar-steiner-extension-complexity-hp) and
[](#lem-planar-steiner-extension-complexity-feldmann),
$\operatorname{xc}(\operatorname{VC}(J))\le\operatorname{xc}(\operatorname{HP}(G',s,t))
\le\operatorname{xc}(P_{\min}(G',\{s,t\}))$. It has $8$ flags per side and $2|E(J)|$ sides, so
$16\cdot52h(h-1)=832h(h-1)$ vertices.

For the four polyhedra, use $H$, which is planar by
[](#lem-planar-steiner-extension-complexity-radial-planar), and
[](#prop-planar-steiner-extension-complexity-steiner). Its vertex count is
$|V(J)|+|E(J)|+\#\text{faces}(J)=104h(h-1)+2$.
```

```{prf:proof} of [](#thm-planar-steiner-extension-complexity) and [](#thm-planar-steiner-extension-complexity-four)
:nonumber:

For two terminals, $n=832h(h-1)\le29^2h^2$, so $(c/29)\sqrt n\le ch$. By
[](#thm-planar-steiner-extension-complexity-reduction),
$\operatorname{xc}(P_{\min}(\Gamma-st,\{s,t\}))\ge\operatorname{xc}(\operatorname{COR}(L_h))
\ge2^{ch}\ge2^{(c/29)\sqrt n}$.

For the four polyhedra, $n=104h(h-1)+2\le11^2h^2$, so the same argument applies with
[](#thm-planar-steiner-extension-complexity-reduction-four) and the constant $c/11$.
```

The construction exists for every $h\ge2$. Since the vertex counts grow quadratically in $h$, this
gives the claimed worst-case lower bound $2^{\Omega(\sqrt n)}$ for graphs with at most $n$ vertices.

## An exact extended formulation from a sphere-cut decomposition

*This section is not formalized.*

```{prf:proposition} Upper bound
:label: prop-planar-steiner-extension-complexity-upper

Each polyhedron in [](#thm-planar-steiner-extension-complexity-main) has an extended formulation of
size $n2^{O(\sqrt n)}$.
```

```{prf:proof} of [](#prop-planar-steiner-extension-complexity-upper)
:nonumber:

Augment the simple planar graph to a triangulation on the same vertices and forbid the added
edges; small graphs can be handled directly. Use a rooted sphere-cut decomposition of its edges,
of width $w=O(\sqrt n)$ and with $O(n)$ nodes [@dorn2010efficient]. An edge of the decomposition
separates two edge sets by a simple closed curve that meets the graph only in the boundary
vertices, which have a cyclic order on the curve. For the partial forest in either disk, record:

1. at each boundary vertex, its degree truncated to $0,1,\ge2$;
2. the partition of the positive-degree boundary vertices by their components in the partial forest;
3. the number of components disjoint from the boundary, truncated at two.

The partition is noncrossing by planarity. At an edge leaf, allow its two possible selections, or
only absence for an added edge. At a merge, add degrees and merge component blocks at shared active
vertices. Test acyclicity with one node per touching component in each child and one edge per shared
vertex active in both children: gluing two forests creates a cycle exactly when this bipartite
multigraph contains one, including a pair of parallel edges. A child component already closed has
no shared vertex. Carry such components forward and add each newly closed one. When the last
incident edge of a vertex has been processed, require positive degree at a terminal and exclude
degree one at a nonterminal. At the root require exactly one component. These operations depend
only on the recorded states, and induction on the decomposition identifies accepting runs with
minimal Steiner trees. For $P_{\mathrm{conn}}$, drop the tests for acyclicity and nonterminal
leaves, keeping all connectivity and terminal tests.

A cyclically ordered set of at most $w$ points has at most $4^w$ noncrossing partitions, and the
degrees already specify the active subset. Hence the number of states, and the number of triples of
states at a binary merge, is $2^{O(w)}$.

For each node, put a nonnegative variable on every allowed local transition. Impose total mass one
on the accepting root transitions. Along each parent–child link and for every shared state, equate
the two marginals of that state. Define $x_e$ as the total mass selecting $e$ at its leaf. This is
the standard passage from dynamic programs to extended formulations
[@martin1990polyhedral; @kaibel2010branched]. To prove exactness, sample a root transition with its
mass. At a child, sample a transition conditional on the state inherited from the parent, using its
local transition masses. The marginal equalities give the conditional distribution whenever the
conditioning state has positive probability, and induction recovers all local marginals and hence
$x$. Conversely, every integral accepting run gives feasible transition masses. This is the full
incidence hull for each bounded connected model. Adding the nonnegative orthant to $P_{\min}$, and
then intersecting with the unit box, gives the other two formulations.
```

An ordinary tree decomposition of width $t$ uses arbitrary boundary partitions, which gives a
standard $n2^{O(t\log(t+1))}$ bound for these connectivity states. The MSO extension theorem of
@kolman2020extension also gives $f(t)\,n$ for fixed treewidth, using the incidence graph with
terminal and edge labels.

## Nonnegative objectives and the terminal parameter

*This section is not formalized.*

Feldmann and Rai [@feldmann2021extended, Theorem 2] construct an LP of size $O(3^km+2^kn)$ whose edge projection $U$
contains $P_{\min}$ and attains its correct minimum for every nonnegative edge-cost vector. This
implies $U+\mathbb R^E_{\ge0}=D$: a point outside $D$ can be strictly separated from it by a lower
supporting inequality with nonnegative normal, because the recession cone of $D$ contains every
positive coordinate ray. Their LP, with $m$ added inequalities, is therefore an exact extended
formulation of $D$, and imposing the box gives one of $P_{\uparrow}$. For $k=2$, send a unit $s$-$t$
flow in the bidirected graph and bound the sum of the two flows on each edge by $x_e$. Flow
decomposition gives exactly $D$, with $O(m)$ inequalities. By contrast,
[](#thm-planar-steiner-extension-complexity-hp) and
[](#lem-planar-steiner-extension-complexity-feldmann) exclude even a bound $f(k)n^{O(1)}$ for
$P_{\min}$.

```{prf:theorem} The terminal parameter
:label: thm-planar-steiner-extension-complexity-param

For every fixed $d$, there is no upper bound $n^d2^{o(k)}$ on the exact extension complexity of
planar Steiner tree dominants. The same holds for $P_{\uparrow}$.
```

The only gadget needed as a black box is the two-selector case of the verification gadget of
Kisfaludi-Bak, Nederlof and van Leeuwen [@kisfaludibak2020nearly, Lemma 4.9 and Fig. 7] (Lemma 23
in the first arXiv version). In their
notation take $L=2$. For any $B$ horizontal indices and any sets $S_1,S_2\subseteq[B]$, it is a plane
graph with $O(B^2)$ vertices, positive internal edge costs, and exterior ports
$p[1],\ldots,p[B],\ w[1],w[2],\ q[B],\ldots,q[1]$ in this cyclic order. A connected subgraph meeting
$p[i],q[j]$ and $w[y]$ costs at least a common value $C_B$. At equality $i=j$, it uses a single
selector edge, incident with $w[y]$, and $i\in S_y$. Conversely, every allowed $(i,y)$ attains
equality. A used $w$-port needs an incident selector edge inside the gadget.

```{prf:proof} of [](#thm-planar-steiner-extension-complexity-param)
:nonumber:

We use a rectangular variant of the grid construction of
[@kisfaludibak2020nearly, Sections 4.3–4.4]. Take $l$ rows, $r$ columns, row labels $s\in[A]$,
binary column labels $y\in\{1,2\}$, and allowed pairs $M_{gj}\subseteq[A]\times\{1,2\}$ for each
cell, and assume that a consistent labelling exists. Put $B=2A$, $i(s,y)=2(s-1)+y$ and
$\bar i=B+1-i$.

A cell consists of a west and an east copy of the gadget. Its west sets are
$S_y=\{i(s,y):(s,y)\in M_{gj}\}$, and its east sets use the reflected indices
$\overline{i(s,y)}$. For every $i$ insert a distinct *join edge* between $q^W[i]$ and
$q^E[\bar i]$. Between successive cells of a row, create a vertex $f[s]$ for each $s$, adjacent to
the preceding east ports $p^E[\overline{i(s,1)}],p^E[\overline{i(s,2)}]$ and the following west
ports $p^W[i(s,1)],p^W[i(s,2)]$. A common root is adjacent to all first west $p$-ports, and the
terminal at the end of each row is adjacent to all last east $p$-ports. These root, end, fuse and
join edges are the *row edges*. In each column, link the west $w$-ports of row $g$ to the east
$w$-ports of row $g+1$ by an eight-cycle alternating four new terminals and the four ports, in
cyclic order $w^W[1],w^W[2],w^E[1],w^E[2]$, so that opposite ports have the same label. At each
exposed top or bottom pair add a fresh terminal adjacent to both ports. The port order gives the
embedding of [@kisfaludibak2020nearly, Fig. 8].

Take three successive minimizing faces. First minimize the sum of the degrees at the new column
terminals. Each needs degree at least one, and a consistent labelling attains equality everywhere,
so on this face the column connections are leaves and cannot connect different rows. Next minimize
the number of row edges. A path from the root to a row end needs a join in each cell, two edges at
every internal fuse and one at each end, so at least $3r$ row edges per row; a consistent labelling
attains this. At equality there is exactly one join per cell and one traversed fuse per gap, and
each half-cell contains a connected subgraph joining its used $p$-, $q$- and $w$-ports. Third,
minimize the internal gadget costs, with lower bound $2lrC_B$ attained by consistent labellings.
At equality the gadget lemma, the joins, the fuses and the eight-cycles force one allowed pair per
cell, consistent along rows and columns; conversely, every consistent labelling lifts. The three
nonnegative objectives together charge every edge, so a positive lexicographic combination exposes
the same face in the dominant and in the bounded upward hull.

Now fix $b\ge3$, split $r$ free bits into $b$ equal blocks, and use $l=\binom b2$ rows indexed by
pairs of blocks, each row label being an assignment to its two blocks, so $A=2^{2r/b}$. Column $j$'s
label is bit $j$; if bit $j$ belongs to the row's blocks, allow only the pairs agreeing on it. The
consistent labellings are precisely the assignments of the $r$ bits. Summing suitable join
coordinates of a fixed cell yields every product of two bits, so the face projects onto
$\operatorname{COR}(K_r)$, and $\operatorname{xc}(\operatorname{COR}(K_r))\ge2^{c r}$ for an absolute
$c>0$ [@fiorini2015exponential; @kaibel2015short]. The instance has $n=O_b(r2^{4r/b})$ vertices and
$k=4(l-1)r+2r+l+1=O_b(r)$ terminals. Given $d$, fix $b>\max(2,8d/c)$. A bound $n^d2^{o(k)}$ would
have base-two logarithm at most $4dr/b+O_b(\log r)+o(r)<cr$ for large $r$, a contradiction.
```

@marx2018subexponential prove a separate lower bound for algorithmic running time under ETH. The
argument above uses the later journal verifier. For the weights printed in Lemma 7.5 of the first
preprint version [@marx2017subexponential], the canonical path uses $N-i$ vertical edges of weight
$M_3$ and an exit of weight $iM_3$, contributing $NM_3$ in total, while the displayed budget is
$(N-1)M_3$. The journal formulation [@kisfaludibak2020nearly, Lemmas 4.8–4.9] uses $NM_3$.

## Special cases, facets and approximations

*This section is not formalized.*

**All vertices terminal.** If $T=V$, $P_{\min}$ is the spanning tree polytope, which has an $O(n)$
planar extended formulation [@validi2019note]. The dual complement of a primal tree using $s$
vertices is connected and has cycle rank $n-s$, by Euler's formula, so for a spanning tree the rank
is zero. In Williams' primal–dual formulation, the primal root must be incident with the chosen dual
root face; Validi and Buchanan give the corrected statement. @goemans1994steiner gives a polyhedral
description for a vertex-weighted tree model on series-parallel graphs.

**Direct inequalities.** Let $G=K_{2,q}$ with the two hubs as terminals. Its $q$ minimal paths form a
simplex. Its dominant has $2^q$ distinct cut facets, although its flow extension has linear size.
Choose a set $B$ containing one edge of each arm. The inequality $x(B)\ge1$ is valid. On equality,
the $q$ orthant rays on the other edges and the $q-1$ differences from one fixed arm-path vector to
the other arm-path vectors span $2q-1$ independent directions, since the differences have rank $q-1$
on the $B$ coordinates. The dominant is full-dimensional in $\mathbb R^{2q}$, so the inequality
defines a facet.

**Approximation and symmetry.** @borradaile2009approximation give a polynomial-time approximation
scheme for planar Steiner tree with nonnegative costs. For general graphs the bidirected cut
relaxation has a polynomial-size flow representation and integrality gap strictly below two
[@byrka2024bidirected]. A fixed-factor approximation may omit the exact faces used in the lower
bounds, so these proofs leave its extension complexity open. The symmetric spanning-tree lower bound
of @pokutta2026approximate concerns the spanning tree polytope of the complete graph and a
restricted class of extensions. The unrestricted correlation-polytope lower bound is due to
@fiorini2015exponential.

## The formalization

The Lean development is self-contained apart from Mathlib [@mathlib2020lean].
[](#def-planar-steiner-extension-complexity-planar) is a structure `PlanarFaces`. The statements
are collected in `Statement.lean`; each is a proposition about the objects `COR`, `grid`, `Pmin`,
`Pconn`, `Pup`, `Dom`, extension complexity `xc` and `IsPlanar`:

```{literalinclude} ../../lean/Lemmata/PlanarSteinerXC/Statement.lean
:language: lean
:start-after: -- DOCS_BEGIN_STATEMENT
:end-before: end Lemmata.PlanarSteinerXC
```

The four main theorems prove them:

```{literalinclude} ../../lean/Lemmata/PlanarSteinerXC/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

| Module | Content |
|---|---|
| `Polyhedral` | LP extensions, `xc`, monotonicity under faces and affine images |
| `Objects` | `Pmin`, `Pconn`, `Pup`, `Dom`, `HP`, `VC`, `COR`, `grid` |
| `TwoTerminal` | [](#lem-planar-steiner-extension-complexity-feldmann) |
| `CoverGraph` | cover graphs of formulas, product formulas, [](#lem-planar-steiner-extension-complexity-cover) |
| `FaceSystem` | [](#def-planar-steiner-extension-complexity-planar), links |
| `Radial`, `RadialFaces` | $H$, [](#lem-planar-steiner-extension-complexity-radial), [](#prop-planar-steiner-extension-complexity-steiner), [](#lem-planar-steiner-extension-complexity-radial-planar) |
| `Duality`, `CycleSpace`, `ForestDual` | flag systems, [](#lem-planar-steiner-extension-complexity-duality), minimal cuts, 2-regular spanning subgraphs, faces avoiding a forest |
| `FlagGraph`, `FlagFaces` | the flag system of $H$, its counts, connectivity, [](#lem-planar-steiner-extension-complexity-flag-planar) |
| `HamiltonDecode`, `HamiltonEncode` | [](#thm-planar-steiner-extension-complexity-hp) |
| `Pendant` | [](#lem-planar-steiner-extension-complexity-pendant) |
| `GridBasic` … `GridPlanar` | the grid, its planar cyclic order and [](#lem-planar-steiner-extension-complexity-grid-planar) |
| `Assembly`, `Main` | the reductions and the lower bounds |

```{include} ../_generated/verification/planar-steiner-extension-complexity.md
```
