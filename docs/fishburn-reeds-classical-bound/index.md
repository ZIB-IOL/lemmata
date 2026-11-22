---
title: The exact classical value of the Fishburn–Reeds matrices
---

```{include} ../_generated/provenance/fishburn-reeds-classical-bound.md
```

The $D_d$ root system gives a Bell inequality with $N=d(d-1)$ settings per party. Its vector value has been known since the original construction [@fishburn1994bell; @epping2013designing]. The difficulty is to bound two independent lists of classical signs. @marton2026exact obtained the exact values for $N=72$ and $90$ by branch-and-bound and stated the general ratio as a conjecture. We prove it in every dimension. The equality cases also answer a separate question about modifying the diagonal.

## The fixed matrix

For each $i<j$ take the two rows $e_i+e_j,e_i-e_j$ of $V\in\mathbb{R}^{N\times d}$. Write $G=VV^\top$, $P=G/2$, and $F_t=3G-tI=6(P-(t/6)I)$. Let $C(t)=\max_{a,b\in\{-1,1\}^N}a^\top F_tb$. Let $Q_d(t)$ be the corresponding maximum of $\sum_{v,w}(F_t)_{vw}\langle A_v,B_w\rangle$ over unit vectors $A_v,B_w\in\mathbb R^d$.

```{prf:theorem} The fixed Fishburn–Reeds shift
:label: thm-fishburn-reeds-classical-bound

For every $d\ge2$,
$$
 C(4)=2N(2d-3),\qquad Q_d(4)=2N(3d-5),\qquad
 \frac{Q_d(4)}{C(4)}=\frac{3d-5}{2d-3}.
$$
```

```{prf:proposition} The all-plus classical strategy
:label: prop-fishburn-reeds-classical-bound-all-plus

The value of $F_4$ at $a=b=\mathbf1$ equals $H=2N(2d-3)$.
```

```{prf:proof} of [](#prop-fishburn-reeds-classical-bound-all-plus)
:nonumber:

Each coordinate pair contributes $2e_i$ to $\alpha=V^\top\mathbf1$. Thus $\alpha=(2(d-1),2(d-2),\ldots,0)$, $\|\alpha\|^2=2N(2d-1)/3$, and $3\|\alpha\|^2-4N=H$.
```

## The upper bound

Fix sign vectors $a,b$, put $p=V^\top a$, and write $y_v=v\cdot p$ for each row $v$. Every coordinate of $p$ is a sum of $2(d-1)$ signs and is therefore even. Two lemmas carry the proof.

```{prf:lemma} The envelope bound
:label: lem-fishburn-reeds-classical-bound-envelope

Let $p\in(2\mathbb Z)^d$ and put
$$
 E(p)=\sum_{i<j}\bigl(\max(4,6|p_i+p_j|-4)+\max(4,6|p_i-p_j|-4)\bigr)-3\|p\|^2 .
$$
Then $E(p)\le H$, except that $E(p)\le H+4$ when exactly two coordinates of $p$ vanish.
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-envelope)
:nonumber:

Write $p_i=2z_i$ and $n_i=|z_i|$. For an integer $w$, $\max(4,12|w|-4)=12|w|-4+8\cdot\mathbf 1[w=0]$, and $|z_i+z_j|+|z_i-z_j|=2\max(n_i,n_j)$. Since $\mathbf 1[z_i=z_j]+\mathbf 1[z_i=-z_j]=\mathbf 1[n_i=n_j]+\mathbf 1[n_i=n_j=0]$, the two rows of the pair $\{i,j\}$ contribute
$$
 g(n_i,n_j)=24\max(n_i,n_j)-8+8\cdot\mathbf 1[n_i=n_j]+8\cdot\mathbf 1[n_i=n_j=0].
$$
So $E(p)=W(n):=\sum_{i<j}g(n_i,n_j)-12\sum_in_i^2$, a symmetric function of the multiset of the $n_i$. Write $H(d)=2d(d-1)(2d-3)$. We prove $W(n)\le H(d)$, plus four when exactly two $n_i$ vanish, by induction on $d$. Let the largest value $m$ occur $k\ge1$ times, and let $\ell=d-k$ smaller values remain. If $m=0$, all values vanish and $W=4d(d-1)$, while $H(d)-4d(d-1)=2d(d-1)(2d-5)$ is negative only for $d=2$, where it equals $-4$. If $m>0$, the copies of $m$ add $12k(k-1)m+k\ell(24m-8)-12km^2$ to $W$ and leave the zero count unchanged, and
$$
 H(\ell+k)-H(\ell)-\bigl(12k(k-1)m+k\ell(24m-8)-12km^2\bigr)=k\bigl(3(2(m-\ell)-k+1)^2+(k-1)(k-3)\bigr).
$$
This is nonnegative: for $k\ge3$ both terms are, for $k=1$ the second vanishes, and for $k=2$ the square is odd and hence at least one.
```

```{prf:lemma} Two vanishing coordinates
:label: lem-fishburn-reeds-classical-bound-two-zeros

If exactly two coordinates of $p=V^\top a$ vanish, then $a_v(v\cdot p)\le-2$ for some row $v$.
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-two-zeros)
:nonumber:

Let $p_k=p_l=0$ with $k\ne l$, all other coordinates nonzero, and suppose $a_v(v\cdot p)\ge-1$ for every row. Since $v\cdot p$ is even, $a_v(v\cdot p)\ge0$. Take a nonzero coordinate $o$. If $k>o$, the rows $e_k\pm e_o$ have values $\pm p_o$, so their signs are $\pm\operatorname{sign}p_o$, and their contributions to $p_k$ cancel. If $o>k$, both rows $e_o\pm e_k$ have value $p_o$ and sign $\operatorname{sign}p_o$, and their contributions $\pm\operatorname{sign}p_o$ to $p_k$ cancel. The same holds for $l$. So $p_k$ and $p_l$ come only from the two rows joining $k$ and $l$: with signs $a_+,a_-$, the larger index receives $a_++a_-$ and the smaller $a_+-a_-$. Both vanish only if $a_+=a_-=0$, which is impossible.
```

```{prf:proof} of [](#thm-fishburn-reeds-classical-bound)
:nonumber:

The all-plus strategy attains $H$ by [](#prop-fishburn-reeds-classical-bound-all-plus). For the upper bound, $(F_4a)_v=3y_v-4a_v$, so
$$
 a^\top F_4b\le\sum_v|3y_v-4a_v|=\sum_v\max(4,6a_vy_v-4)-3\|p\|^2,
$$
because $|3y-4a_v|=\max(4,6a_vy-4)-3a_vy$ for $a_v=\pm1$ and $\sum_va_vy_v=\|p\|^2$. Replacing each $a_vy_v$ by $|y_v|$ does not decrease a term, and increases it by at least four when $a_vy_v\le-2$. So $a^\top F_4b\le E(p)$, and $a^\top F_4b\le E(p)-4$ if some row has $a_vy_v\le-2$. By [](#lem-fishburn-reeds-classical-bound-envelope), $E(p)\le H$ unless exactly two coordinates of $p$ vanish; then $E(p)\le H+4$ and [](#lem-fishburn-reeds-classical-bound-two-zeros) supplies such a row. Hence $a^\top F_4b\le H$, and $C(4)=H$.

For the vector problem, $V^\top V=2(d-1)I$ because the two rows of each pair cancel their off-diagonal contributions. Put $L=6(d-1)$. Stacking the two lists of unit vectors and applying Cauchy–Schwarz gives $Q_d(t)\le N\max(|L-t|,|t|)$. Since $F_tV=(L-t)V$, the unit roots $v/\sqrt2$ attain $N(L-t)$ for $t\le L/2$. This covers $t=4$ for $d\ge3$. At $d=2$, $F_t=(6-t)I$. Hence $Q_d(4)=2N(3d-5)$, and the ratio follows.
```

The original unshifted family has ratio $3(d-1)/(2d-1)$; Fishburn and Reeds obtained the shifted $20\times20$ example with ratio $10/7$ [@fishburn1994bell]. The all-order assertion here fixes that same shift. The Lean rows are $e_i\pm e_j$ with $j<i$; reversing the coordinates identifies them with the rows above.

## Optimal strategies

The structure of the maximizers, and the shifted matrices on the [companion page](shifts.md), use an exact identity for the value.

```{prf:lemma} The midpoint identity
:label: lem-fishburn-reeds-classical-bound-midpoint

For sign vectors $a,b$, put $s=(a+b)/2$, $w=(a-b)/2$, $u=V^\top s$, and $z=V^\top w$. At the fixed shift,
$$
 a^\top F_4 b=4N+3\|u\|^2-8|\operatorname{supp}s|-3\|z\|^2 .
$$
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-midpoint)
:nonumber:

On every row exactly one of $s,w$ is nonzero. Polarization gives $a^\top G b=\|u\|^2-\|z\|^2$ and $a^\top b=2|\operatorname{supp}s|-N$.
```

The same identity holds at $t$ with $4N,8$ replaced by $tN,2t$. Write $x_0\le\cdots\le x_{d-1}$ for the sorted magnitudes of $u$. Put $r_j=2j-x_j$, $c_t(k)=(2t-6k)_+$, and $h_+=\max(h,0)$. The exact rowwise loss in replacing $6s_v(v\cdot u)-2t|s_v|$ by its largest value over $s_v\in\{0,\pm1\}$ is nonnegative. Denote the sum of these losses by $D$. For $t\ge0$ we have

$$
 a^\top F_t b=N(4d-2-t)
 +\sum_{i<j}\{c_t(x_j-x_i)+c_t(x_j+x_i)\}
 -3\sum_j r_j^2-3\|z\|^2-D.
$$ (eq-fishburn-reeds-classical-bound-squares)

Indeed, replace $3\|u\|^2$ by $-3\|u\|^2+6\sum_v s_v(v\cdot u)$. Expand $(6|v\cdot u|-2t)_+$ and use $|y+x|+|y-x|=2\max(|x|,|y|)$ for each coordinate pair. Completing the squares against $2j$ gives [](#eq-fishburn-reeds-classical-bound-squares).

Let $D_d=\{y\in\mathbb Z^d:\sum_i y_i\text{ is even}\}$. All roots belong to $D_d$. Since $\alpha-u-z=V^\top(\mathbf1-a)\in2D_d$, the coordinates of $z$ are odd precisely where those of $u$ are odd. The number of odd coordinates is even. If all $x_j$ are even and $\sum_j x_j\not\equiv N\pmod4$, then $z$ is a nonzero even vector and $\|z\|^2\ge4$. This follows because changing signs of even entries preserves their sum modulo four, and $\sum_i\alpha_i=N$.

At $t=4$ and $t=6$, both corrections in [](#eq-fishburn-reeds-classical-bound-squares) vanish across any consecutive gap of size at least two. Split the sequence at these gaps. In one of the resulting blocks, charge $p(r)=3r^2+3\mathbf1_{r\ {\rm odd}}$ at each position. This spends only the odd-coordinate part of $3\|z\|^2$. The **block score** is its pair corrections less these charges. Residuals increase by one or two at each step. Only the block containing zero can have a sum correction.

At $t=4$, the two nonzero correction weights are $c_4(0)=8$ and $c_4(1)=2$.

```{prf:lemma} Positive blocks
:label: lem-fishburn-reeds-classical-bound-positive

A positive block has score at most zero. If an odd coordinate occurs, its score is at most $-4$.
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-positive)
:nonumber:

If the block is all even, it is constant. For length $k$ and mean residual $\delta$ its score is $k(k-1)(3-k)-3k\delta^2$. For even $k$, $\delta$ is an odd integer. The score is nonpositive, with equality exactly for a singleton or triple centered on its targets.

Suppose some coordinate is odd. Remove an endpoint whose residual has largest magnitude $R$. A contributing partner $g$ places away has coordinate difference at most one, hence residual difference at least $2g-1$ and at most $2R$. There are at most $R$ partners. For $R\ge3$ the endpoint contributes at most $8R-p(R)\le-6$. Continue until all remaining residuals lie in $[-2,2]$. If an odd coordinate remains, an endpoint of magnitude two can earn at most $8+2$ against its cost of $12$. Indeed, two equal-coordinate partners would use all three residuals $-2,0,2$ in succession, exhausting the possible span and leaving no odd coordinate. After removing these endpoints, the residuals belong to $\{-1,0,1\}$. One odd costs six and earns at most two. Two odds cost twelve and earn at most eight altogether. If all odds disappeared earlier, at least six was spent and the remaining all-even block is nonpositive. Every positive block containing an odd coordinate therefore has score at most $-4$.
```

```{prf:lemma} The block starting at zero
:label: lem-fishburn-reeds-classical-bound-zero

For a block starting at zero, its score is at most $4\mathbf1_{\text{block}=(0,0)}$.
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-zero)
:nonumber:

Within this block $0\le x_j\le j$. Appending zero at position $j$ contributes $16j-12j^2$. If $x_j>0$, any earlier coordinate contributes at most eight, including the pair $(0,1)$, whose two corrections total four. Thus for $j\ge3$ the increment is at most $8j-3j^2<0$. At $j=1$, the two possible scores are $4$ and $-2$. At $j=2$, appending zero contributes $-16$, appending one contributes at most $16-27-3$, and appending two forces $(0,1,2)$, with increment $2-12$. Every word of length at least three has strictly negative score. Thus $(0,0)$ attains four and the only word of score zero is the singleton $(0)$.
```

```{prf:proposition} Disagreements in optimal strategies
:label: prop-fishburn-reeds-classical-bound-disagreements

The largest number of rows on which a maximizing pair of sign vectors disagrees is $3\lfloor d/3\rfloor$.
```

```{prf:proof} of [](#prop-fishburn-reeds-classical-bound-disagreements)
:nonumber:

By [](#eq-fishburn-reeds-classical-bound-squares) and the charges above, $a^\top F_4b$ is at most $H$ plus the block scores, minus $D$ and minus the part of $3\|z\|^2$ not spent on odd coordinates. By the two block lemmas every block score is nonpositive, except four for a block of exactly two zeros, and such a block cannot occur in a maximizing pair. If either internal root $e_i\pm e_j$ is placed in $s$, the row loss $D$ pays eight. If both are in $w$, they contribute $\pm2$ to one of the two zero coordinates of $z$. Each incident root from outside the block placed in $w$ pays at least four in $D$, since its absolute projection on $u$ is at least two. With zero, one, or at least two such outside roots, the combined cost from $D$ and these two coordinates of $3\|z\|^2$ is at least $12$, $7$, or $8$, respectively. This exceeds the exceptional score of four and leaves all odd-coordinate charges available elsewhere.

At equality all positive blocks are centered singletons or triples, with a possible singleton zero, and $D=0$. Because the threshold $4/3$ is nonintegral, a row is in $w$ exactly when $|v\cdot u|\le1$. A triple contributes its three difference roots and a singleton contributes none, after signing and ordering the coordinates. Conversely, form $\lfloor d/3\rfloor$ disjoint consecutive triples of targets. Keep $s_v=1$ outside the internal difference roots. Put those roots in $w$ with cyclic orientations. Their signed sum is zero, and $u$ replaces each triple of targets by its mean. This loses eight in $\|u\|^2$ per triple and gains three disagreements, attaining $H$ with $3\lfloor d/3\rfloor$ disagreements.
```

For the archived matrices $F_{72}$ and $F_{90}$, the classical/vector pairs are $(2160,3168)$ and $(3060,4500)$. Their ratios are $22/15$ and $25/17$, in agreement with Eq. (26) of @marton2026exact. The [archived matrices](https://github.com/istvanmarton/IBB/tree/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844/Examples) use lexicographic pairs, with the plus root first. Every one of their 13,284 entries agrees with $3VV^\top-4I$ in that order.

## A different question about the diagonal

The [companion page](shifts.md) proves the zero-diagonal formula, determines all shifts between $4$ and $6$, and gives the global optimal uniform shifts in dimensions seven through ten. In particular, the statement in §III.2 of @designolle2026better that the $2/3$ shift in $P-\lambda I$ remains optimal in dimensions seven and eight is contradicted by $P-I$ in both dimensions. The same extension to $d=6,7,8$ appears in arXiv:2409.03739v4, §III.2. Its fixed-shift values agree with the formula proved above. The comparison concerns the scalar family $P-\lambda I$. Determining $K_G(d)$ requires a supremum over all Bell matrices, and facet status is a separate geometric assertion.

## Scope of the Lean source

The Lean source proves [](#thm-fishburn-reeds-classical-bound) in every order $d\ge2$ along the proof given here: [](#lem-fishburn-reeds-classical-bound-envelope) and [](#lem-fishburn-reeds-classical-bound-two-zeros) for the classical value and the spectral bound for the vector value; its vector bound holds for unit vectors in every dimension. It also proves the all-plus witness, the midpoint identity, both block bounds and the comparison of the two shift formulas. The zero-block export gives the upper inequality with its unique positive exception; strictness for the other nonsingleton words follows from the displayed increments. [](#prop-fishburn-reeds-classical-bound-disagreements), the interval theorem and the global optima on the companion page, and the asymptotic estimate have mathematical proofs here; the finite optimization certificates also have an independent executable verifier.

```{literalinclude} ../../lean/Lemmata/FishburnReedsClassicalBound/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/fishburn-reeds-classical-bound.md
```
