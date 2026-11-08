---
title: The Covering Radius of the Reed-Muller Code RM(5,9) Is 32
---

```{include} ../_generated/provenance/rm59-upper.md
```

The Reed–Muller code $\mathrm{RM}(r,m)$ consists of the Boolean polynomials in $m$ variables of degree at most $r$, viewed as functions on $\mathbb F_2^m$ [@reed1954class; @muller1954application]. For a Boolean function $f$, write $\operatorname{wt}(f)=|\{x:f(x)=1\}|$ and $d(f,\mathrm{RM}(r,m))=\min_{p\in\mathrm{RM}(r,m)}\operatorname{wt}(f+p)$. The covering radius is the maximum of this distance over all Boolean functions:

$$
\rho(\mathrm{RM}(r,m))
=\max_{f:\mathbb F_2^m\to\mathbb F_2}d(f,\mathrm{RM}(r,m)).
$$

We prove the following upper bound.

::::{prf:lemma}
:label: lem-rm59-upper-bound

Every Boolean function $f:\mathbb F_2^9\to\mathbb F_2$ admits a Boolean polynomial $p$ of degree at most five such that $\operatorname{wt}(f+p)\le32$.

::::

(rm59-table-exact)=
Together with the previous lower bound of @khoruzhii2026minrank, [](#lem-rm59-upper-bound) gives $\rho(\mathrm{RM}(5,9))=32$.

## Previous bounds

@dougherty2022covering proved $28\le\rho(\mathrm{RM}(5,9),\mathrm{RM}(6,9))\le32$, where the relative covering radius restricts the maximum to the indicated outer code. @khoruzhii2026weight obtained the upper bound $32$ for the relative covering radius of $\mathrm{RM}(6,10)$ in $\mathrm{RM}(7,10)$. The matching lower bounds of @khoruzhii2026minrank determine both relative radii to be $32$.

:::{table} Full covering radii $\rho(\mathrm{RM}(r,m))$ for $6\le m\le10$ and $1\le r\le6$. Intervals $[L,U]$ give lower and upper bounds. Updated from Table 1 of @gao2026numerical; each entry links to its source or derivation.
:label: tab-rm59-covering-radii

| $m\backslash r$ | 1 | 2 | 3 | 4 | 5 | 6 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | [28](#rm59-table-bent) | [18](doi:10.1109/TIT.1981.1056364) | [8](doi:10.1137/0137032) | [2](#rm59-table-hamming) | [1](#rm59-table-parity) | [0](#rm59-table-full) |
| 7 | [56](doi:10.1109/TIT.1980.1056187) | [40](doi:10.1016/j.disc.2019.111625) | [20](doi:10.1109/TIT.2023.3242966) | [8](doi:10.1137/0137032) | [2](#rm59-table-hamming) | [1](#rm59-table-parity) |
| 8 | [120](#rm59-table-bent) | \[[88](#rm59-table-rm28), [91](#rm59-table-rm28)\] | [56](doi:10.48550/arXiv.2611.03186) | [26](doi:10.3934/amc.2023038) | [10](doi:10.1137/0137032) | [2](#rm59-table-hamming) |
| 9 | [242](doi:10.48550/arXiv.2610.17871) | \[[196](doi:10.1109/ITW.2003.1216724), [211](#rm59-table-recursive-nine)\] | \[[112](#rm59-table-sphere), [147](#rm59-table-recursive-nine)\] | \[[59](#rm59-table-sphere), [82](#rm59-table-recursive-nine)\] | [32](#rm59-table-exact) | [10](doi:10.1137/0137032) |
| 10 | [496](#rm59-table-bent) | \[[408](doi:10.48550/arXiv.2607.02365), [453](#rm59-table-recursive-ten)\] | \[[271](#rm59-table-sphere), [358](#rm59-table-recursive-ten)\] | \[[162](#rm59-table-sphere), [229](#rm59-table-recursive-ten)\] | \[[77](#rm59-table-sphere), [114](#rm59-table-recursive-ten)\] | \[[32](#lem-cocubic-covering-ten), [42](#rm59-table-recursive-ten)\] |

:::

:::{admonition} Sources and bounds
:class: dropdown

(rm59-table-full)=
The code $\mathrm{RM}(m,m)$ contains all Boolean functions on $\mathbb F_2^m$, so its covering radius is $0$.

(rm59-table-parity)=
The code $\mathrm{RM}(m-1,m)$ consists of all words of even weight, so its covering radius is $1$. This is the parity-check code of @hamming1950error, Section 2.

(rm59-table-hamming)=
For $m\ge2$, the code $\mathrm{RM}(m-2,m)$ is the extended Hamming code [@hamming1950error, Sections 3–4]. Its parity-check matrix has columns $(1,x)$ for $x\in\mathbb F_2^m$. Every syndrome is a sum of at most two columns, and a syndrome $(0,y)$ with $y\ne0$ requires two, giving covering radius $2$.

(rm59-table-bent)=
For even $m$, bent functions give $\rho(\mathrm{RM}(1,m))=2^{m-1}-2^{m/2-1}$ [@rothaus1976bent].

(rm59-table-rm28)=
The preprint of @hou2026second gives $88\le\rho(\mathrm{RM}(2,8))\le91$.

(rm59-table-sphere)=
The sphere-covering bound can be applied separately to even and odd words, since every codeword has even weight for $r<m$. With $N=2^m$ and $k=\sum_{i=0}^r\binom mi$, each parity must satisfy $\sum_{0\le j\le t,\ j\equiv\varepsilon\pmod2}\binom Nj\ge2^{N-k-1}$ for $\varepsilon=0,1$. The least admissible $t$ gives the lower bounds $112$, $59$, $271$, $162$, and $77$ for $(r,m)=(3,9),(4,9),(3,10),(4,10),(5,10)$, respectively.

(rm59-table-recursive-nine)=
The standard recurrence $\rho(\mathrm{RM}(r,m))\le\rho(\mathrm{RM}(r-1,m-1))+\rho(\mathrm{RM}(r,m-1))$ gives the nine-variable upper bounds $211=91+120$, $147=91+56$, and $82=56+26$, using the results of @hou2026second, @rothaus1976bent, @zhao2026covering, and @gillot2024covering.

(rm59-table-recursive-ten)=
Applying the same recurrence in ten variables gives $453=211+242$, $358=147+211$, $229=82+147$, $114=32+82$, and $42=10+32$. Here $242$ is the first-order radius from @wang2026firstorder, while the last two bounds use [](#lem-rm59-upper-bound).

:::

## Moment matching

The proof represents a coset by its moments through degree three. We first match the moments through degree two by an affinely independent set, then complete the cubic moments while controlling the intersection with that set.

For a set $S\subseteq\mathbb F_2^m$ and a coordinate set $I\subseteq\{1,\ldots,m\}$, define $\mu_I(S)=\sum_{x\in S}\prod_{i\in I}x_i$, with the sum taken in $\mathbb F_2$. Matching these moments for $|I|\le d$ is equivalent to matching the sums of every Boolean polynomial of degree at most $d$.

In nine variables, two supports with the same moments through degree three represent the same coset of $\mathrm{RM}(5,9)$. Indeed, let $h$ be the sum of their indicator functions. The coefficient of the monomial $\prod_{i\in B}x_i$ in the algebraic normal form of $h$ is

$$
a_B=\sum_{x\in\mathbb F_2^9}h(x)\prod_{i\notin B}(1+x_i).
$$

If $|B|\ge6$, expanding the product expresses $a_B$ as a sum of moments of degree at most three, all zero. Thus $h$ has degree at most five.

::::{prf:lemma}
:label: lem-rm59-upper-simplex

Every set $S\subseteq\mathbb F_2^m$ of odd cardinality admits an affinely independent set $P\subseteq\mathbb F_2^m$ such that $\sum_{x\in P}q(x)=\sum_{x\in S}q(x)$ for every Boolean polynomial $q$ of degree at most two.

::::

::::{prf:proof} of [](#lem-rm59-upper-simplex)
:nonumber:

Choose a set $P$ of minimum cardinality with the required moments. Its cardinality is odd, by the constant moment. If $P$ is affinely dependent, it contains a nonempty even set $Q$ with $\sum_{x\in Q}x=0$. Since $|P|$ is odd, choose $p\in P\setminus Q$ and $y\in Q$, and put $t=p+y$.

Translation by $t$ preserves the moments of $Q$ through degree two: the additional terms in each translated quadratic moment involve only the constant and linear moments of $Q$, which vanish. Consequently $(P\setminus Q)\mathbin\triangle(Q+t)$ has the same moments as $P$. The two sets in this symmetric difference meet at $p$, so its cardinality is at least two smaller than $|P|$, a contradiction.

::::

For $m=9$, the set $P$ has odd cardinality at most ten, so $|P|\in\{1,3,5,7,9\}$. For a support $S$ with $|S|$ odd, the symmetric difference $H=S\mathbin\triangle P$ therefore has vanishing moments through degree two.

## Cubic forms and intersections

Write $V=\mathbb F_2^9$. A support $H$ with vanishing moments through degree two defines a trilinear form on the dual space $V^*$ by

$$
T_H(\lambda,\mu,\nu)=\sum_{x\in H}\lambda(x)\mu(x)\nu(x).
$$

This form is alternating: when two arguments coincide, the product reduces to a polynomial of degree at most two. Its $\binom93=84$ values on increasing triples of coordinate functionals are precisely the cubic moments of $H$.

The nonzero alternating trilinear forms in nine dimensions fall into $348$ orbits under $\mathrm{GL}(9,2)$, classified by @brier2003classification and @hora2021classification. The contragredient action gives the same orbit classification for forms on $V^*$. We use representatives listed in @khoruzhii2026classification. To avoid assuming completeness of these classifications, we verify the list directly: computed invariants show that the representatives lie in distinct orbits, and upper bounds $U_T$ on their stabilizer orders satisfy

$$
1+\sum_T\frac{|\mathrm{GL}(9,2)|}{U_T}=2^{84}.
$$

Each orbit has size at least $|\mathrm{GL}(9,2)|/U_T$. Thus the identity proves that these disjoint orbits, together with zero, exhaust all $2^{84}$ alternating trilinear forms.

For each cubic form $T$ and each affinely independent set $P$ of odd cardinality, we construct a support $G$ whose moments through degree two vanish, whose cubic form is $T$, and for which

$$
|G\mathbin\triangle P|=|G|+|P|-2|G\cap P|\le31.
$$

We use the induced action $A\cdot T_H=T_{AH}$. If $A\in\mathrm{GL}(9,2)$ maps $T$ to a catalogue representative $T_0$, it suffices to construct $G_0$ for $T_0$ and the set $AP$, and put $G=A^{-1}G_0$. For the zero form, take $G=\varnothing$.

Each nonzero representative has a support of size at most $32$ with vanishing moments through degree two. Every translation of such a support preserves its moments through degree three: expanding a translated monomial introduces only moments of degrees at most two, which vanish. Linear maps stabilizing its cubic form also preserve these moments. We choose among the resulting supports one meeting $P$ in enough points.

Translations suffice for supports of size at most $24$. For sizes $26$ and $28$, finite pair and triple incidence checks provide the required intersections. The two size-$30$ families and the size-$32$ family use geometric constructions over $\mathbb F_2$ and $\mathbb F_8$, giving intersections of size at least $(|P|-1)/2$ for weight $30$ and $(|P|+1)/2$ for weight $32$.

::::{prf:proof} of [](#lem-rm59-upper-bound)
:nonumber:

Put $S=\operatorname{supp}(f)$ and first suppose that $|S|$ is odd. Choose $P$ from [](#lem-rm59-upper-simplex), and apply the intersection construction to the cubic form of $H=S\mathbin\triangle P$. Then $G$ and $H$ have the same moments through degree three, so $G\mathbin\triangle P$ and $S$ also have the same moments. Since $|G\mathbin\triangle P|\le31$, moment matching gives a polynomial $p\in\mathrm{RM}(5,9)$ with $\operatorname{wt}(f+p)\le31$.

If $|S|$ is even, toggle the value of $f$ at any point and apply the odd case. Toggling it back increases the weight by at most one, giving $\operatorname{wt}(f+p)\le32$.

::::

The same approach may also help determine the full covering radius of $\mathrm{RM}(6,10)$.

```{literalinclude} ../../lean/Lemmata/RM59/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/rm59-upper.md
```
