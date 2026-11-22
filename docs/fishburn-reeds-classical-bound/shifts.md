---
title: Uniform diagonal shifts for the Fishburn–Reeds family
---

Use $F_t=3VV^\top-tI=6(P-(t/6)I)$ and the notation of the [fixed-shift theorem](index.md). Put $m=\lfloor d/3\rfloor$.

```{prf:theorem} A full interval of classical values
:label: thm-fishburn-reeds-classical-bound-interval

For $d\ge2$ and $4\le t\le6$,
$$C(t)=H-(t-4)(N-6m).$$
In particular, $C(6)=4N(d-2)+12m$.
```

```{prf:proof} of [](#thm-fishburn-reeds-classical-bound-interval)
:nonumber:

It suffices to analyze $t=6$. Each classical strategy is affine in $t$, so $C$ is convex. The triple strategy in [](#thm-fishburn-reeds-classical-bound) gives the claimed affine function. Once the endpoint values agree, convexity supplies the reverse inequality throughout the interval.

In [](#eq-fishburn-reeds-classical-bound-squares) the positive correction weights are now $12,6$. Write $p(r)=3r^2+3\mathbf1_{r\ {\rm odd}}$ as before. In a positive block of length one or two the score is nonpositive. For a consecutive pair of residuals with step one, the reward is six and costs at least six; for a step two, the reward is twelve and costs at least twelve. For length three the steps, up to reversal, are $(2,2),(1,1),(1,2)$, with respective rewards $36,12,24$. Comparing the translates that minimize the sum of the convex $p$ shows that the only positive residual words are $(-2,0,2)$, of score $12$, and $(-1,0,2),(-2,0,1)$, of score six. For $(1,2)$ the costs at starting residuals $-2,-1,0$ are $24,18,36$. For $(2,2)$ the minimum is $24$ at center zero and the next cost is $42$. For $(1,1)$ the minimum is $12$.

For a block of length at least four, remove an endpoint of largest residual magnitude $R$. At most $R$ partners can interact. For $R\ge4$ its gain is at most $12R-p(R)\le0$, and for a block of length four the gain is at most $36-48=-12$. For $R=3$ a positive gain requires three equal-coordinate partners. This forces the whole word $(-3,-1,1,3)$, of score zero. If a positive triple remains after a deletion from length four, an even triple gives the endpoint at most $3\cdot6-30=-12$. A mixed triple has only one odd residual, so its endpoint earns at most $12+6+6-30=-6$. Finally, when $R\le2$ any word of length at least four occupies four or five of $-2,-1,0,1,2$. All five score $-12$. Omitting one slot of absolute value zero, one or two gives $0,0,-6$, respectively. Induction on length proves that no longer positive block contributes a positive score.

For a zero block, appending zero at index $j$ contributes $24j-12j^2$. A positive coordinate earns at most $12j$ and has $x_j\le j$. At $j=1$ the two possible increments are $12,6$. At $j=2$ the increment for zero is zero, for one is at most $24-27-3=-6$, and for two is $6-12=-6$. At $j=3$ zero costs a net $36$, one or two gains at most $36-48=-12$, and three forces $(0,1,2,3)$, gaining $6-27-3$. Later increments are nonpositive. The positive zero blocks are $(0,0),(0,0,0)$ of score $12$, and $(0,1),(0,0,1)$ of score six.

Allot three coordinates to each positive triple. A positive terminal pair can likewise be allotted three if any unused coordinate remains. The exceptional packing has $d=3m+2$, with $m$ positive triples and that pair. Each mixed positive block has exactly one odd coordinate and loses six against its maximum. Their number must be even. Two such losses pay for the pair. If all blocks are even, the positive triples are centered and preserve their target sums. The last two zeros replace targets $0,2$. The mod-four condition in the fixed-shift proof then forces an additional loss of twelve from $3\|z\|^2$. The total correction after charges is at most $12m$. The triple construction attains it, proving the assertion.
```

## Where the published shift stops being optimal

```{prf:lemma} Comparing the two exact formulas
:label: lem-fishburn-reeds-classical-bound-comparison

For every integer $d\ge7$, with $N=d(d-1)$ and $m=\lfloor d/3\rfloor$,
$$\frac{3d-5}{2d-3}<\frac{6N(d-2)}{4N(d-2)+12m}.$$
```

```{prf:proof} of [](#lem-fishburn-reeds-classical-bound-comparison)
:nonumber:

The equivalent inequality is $3m<N(d-2)/(2(3d-5))$. At $d=7$ this is $6<105/16$. For $d\ge8$, use $3m\le d$ and $(d-1)(d-2)-2(3d-5)=(d-8)^2+7(d-8)+4>0$.
```

The vector numerator on $[4,6]$ is $N(L-t)$ for $d\ge3$. Thus $P-I$ itself improves upon $P-\tfrac23 I$ for every $d\ge7$, and gives $35/24$ and $28/19$ in dimensions seven and eight. Table 1 of @designolle2026better gives $16/11$ and $19/13$ at the fixed shift.

For $3\le d\le6$ the comparison of slopes reverses or is an equality. The all-plus affine lower bound for $C(t)$ on the left of $4$ and the maximal-triple affine lower bound on the right show that $Q_d(t)/C(t)$ never exceeds its value at $4$ while $t\le L/2$. To treat larger $t$, choose signs $a$ with $\|V^\top a\|^2\le4$. Each unordered pair of indices can contribute $\pm2$ to either endpoint. Assign each edge to an endpoint so all indegrees are even except possibly one; orient a spanning tree from the leaves after fixing all other edges, prescribing each leaf's required parity in turn. Balance signs at each vertex. Then $b=-a$ gives $C(t)\ge Nt-12$. For $d\ge4$ the spectral bound yields $Q_d(t)/C(t)\le Nt/(Nt-12)\le9/8$ on this branch. For $d=3$ a single triple gives $C(t)\ge36$. Use $36$ on $[6,8]$ and $6t-12$ for $t\ge8$ to bound the ratio by $4/3$. The shift $t=4$ is therefore globally optimal exactly for $3\le d\le6$ among the nontrivial orders. For $d=2$ every nonzero matrix in the family has ratio one.

## Four global optima

| $d$ | Optimizing $\lambda$ in $P-\lambda I$ | $t=6\lambda$ | $C(t)$ | $Q_d(t)$ | Optimal ratio |
|---:|---:|---:|---:|---:|---:|
| 7 | $4/3$ | $8$ | $804$ | $1176$ | $98/67$ |
| 8 | $6/5$ | $36/5$ | $1320$ | $9744/5$ | $406/275$ |
| 9 | $4/3$ | $8$ | $1944$ | $2880$ | $40/27$ |
| 10 | $14/11$ | $84/11$ | $30780/11$ | $45900/11$ | $85/57$ |

Two sign strategies in each dimension give the affine minorants below. They intersect at the stated $t$, and their slopes bracket $-C(t)/(L-t)$. Consequently at least one bounds the ratio on the entire branch $t\le L/2$. The estimate $9/8$ handles the other branch. The only finite upper bound needed is the classical value at their intersection.

| $d$ | Left supporting line | Right supporting line | Groups, left and right |
|---:|---|---|---|
| 7 | $1044-30t$ | $900-12t$ | $(1,3,3)$ and $(0^4,3)$ |
| 8 | $1608-40t$ | $1536-30t$ | $(0^2,3,3)$ and $(3,5)$ |
| 9 | $2376-54t$ | $2328-48t$ | $(3,3,3)$ and $(0^3,3,3)$ |
| 10 | $3348-72t$ | $3180-50t$ | $(1,3,3,3)$ and $(5,5)$ |

Partition coordinates in ascending target order. For an odd group of size $k$ put its difference roots in $w$, oriented as a regular tournament, with all its sum roots in $s$. Keep both roots of each cross-group pair in $s$ with their original all-plus signs. The $k$ targets flatten to their mean, losing $k(k^2-1)/3$ in squared norm and creating $\binom{k}{2}$ disagreements, with zero net $w$-sum. A group $0^k$ is the bottom $k$ coordinates with both roots of each internal pair in $w$. This loses $4\sum_{j<k}j^2$, creates $k(k-1)$ disagreements, and costs another $4$ or $0$ in $\|z\|^2$ according as $\binom{k}{2}$ is odd or even, by the edge assignment above.

**The upper certificate.** Fix $a$ and maximize over $b$. Write $p_1\le\cdots\le p_d$ for the sorted values $|(V^\top a)_i|/2$. Each signed root pair contributes twice a signed coordinate vector. Thus $p_i$ are integers in $[0,d-1]$, and $\sum p_i\equiv\binom d2\bmod2$. The weights $w_v=|v\cdot V^\top a|/2$ are exactly the multiset $p_j-p_i,p_j+p_i$ for $i<j$. Put $W=\sum w_v$. The set $S$ of positive-weight rows with $a_v$ opposite to $v\cdot V^\top a$ has weight
$$\sum_{v\in S} w_v=(W-2\sum p_i^2)/2,$$
by $\sum a_v(v\cdot V^\top a)=\|V^\top a\|^2$. At $t=A/B>0$, the value against optimal $b$, multiplied by $B$, is
$$\sum_v|6Bw_v-A|+\sum_{v\in S}2\min(6Bw_v,A).$$
The gain per unit weight decreases with positive $w_v$. Allow fractional membership in $S$ and fill weights in increasing order until its budget is exhausted. This bounds the true score from above for each $p$. Exhausting the nondecreasing $p$ gives respectively $804,6600,1944,30780$ in the integer scales $B=1,5,1,11$. The [verifier](verify.cjs) performs the greedy bound with integer cross multiplication, tests the two witnesses per dimension, and can compare the two archived fixed-shift data files entry by entry. Only the four optimal-shift upper certificates use this computation.

## Shifts growing with dimension

For completeness, the optimized ratio can exceed the limiting fixed-shift value $3/2$. For $t\ge0$,
$$ C(t)\le N(4d-2-t)+d\left(\frac{5t^2}{18}+\frac t2+\frac{13}4\right). $$
To see this for $t>0$, reflect the sorted $x$ across zero to form $2d$ consecutive signed coordinates $y$, and reflect the targets $2j$ to $T$ in the same order, duplicating zero. The pair correction in [](#eq-fishburn-reeds-classical-bound-squares) is at most half the sum of $c_t(|y_i-y_j|)$ over the enlarged list. Each original correction occurs twice. The quadratic loss is $(3/2)\sum(T_i-y_i)^2$.

Translate a grid of width $h=t/3$ uniformly over one period and replace $y_i$ by the center $Y_i$ of its bin. A pair at distance $g$ shares a bin with probability $(1-g/h)_+=c_t(g)/(2t)$. The quantization error has mean zero and variance $h^2/12$, which adds $dt^2/36$ to the upper bound after completing the squares. In a bin with $k$ targets, the centered squared sum of a progression of spacing two is $k(k^2-1)/3$. A collapsed central gap separating $p$ coordinates from $q$ loses at most $(8/k)\sum_{i\le p<j}(j-i)=4pq\le k^2$, by the pairwise variance identity. The bin's gain is thus at most $k[t(k-1)-(k^2-1)+3k]/2\le k[(t+3)^2/4-t+1]/2$. Summing over $2d$ targets proves the bound. The case $t=0$ follows directly from (1).

Set $t=3(d-5/2)/5$. Twice $Q_d(t)$ minus three times this upper bound is at least $d[3(d-5/2)^2/10-6(d-1)-39/4]$, positive for every $d\ge26$. The limiting ratio from these bounds is $54/35$. Hence the limit inferior of the optimal family ratios is at least $54/35$. The exact optimal shifts from dimension eleven onward and the exact asymptotic optimum remain open here.

## Reproducibility

```{literalinclude} verify.cjs
:language: javascript
```
