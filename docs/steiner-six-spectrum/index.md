---
title: On the Existence Spectrum of Steiner Systems S(2,6,n)
---

```{include} ../_generated/provenance/steiner-six-spectrum.md
```

A Steiner system $S(2,k,n)$ consists of $n$ points and a family of $k$-element blocks in which every pair of distinct points occurs only once. The Fano plane is an $S(2,3,7)$. Its seven lines are triples, and any two of its seven points determine a unique line.

For $n\ge k$, the existence spectrum for $k=3$ is $n\equiv1,3\pmod 6$ [@kirkman1847combinations]. For $k=4$ and $k=5$, the corresponding spectra are $n\equiv1,4\pmod{12}$ and $n\equiv1,5\pmod{20}$, respectively [@hanani1961existence]. In all three cases the divisibility conditions obtained by counting pairs are sufficient. Six is the smallest block size for which these conditions admit exceptions and the existence spectrum remains incomplete. Each point of an $S(2,6,n)$ lies in $(n-1)/5$ blocks, and there are $n(n-1)/30$ blocks in all. These two numbers are integers if and only if $n\equiv1,6\pmod{15}$.

::::{prf:theorem}
:label: thm-steiner-six-spectrum

Let $n$ be an integer satisfying $n\equiv 1,6\pmod{15}$. A Steiner system $S(2,6,n)$ exists if $n>81$ or $n\in\{31,66,76\}$.

::::

The [Zenodo archive](https://zenodo.org/records/24417862) contains block lists for the 24 new systems and a [C++20 generator](https://zenodo.org/api/records/24417862/files/s26n.cpp/content) for every order $n<10000$ covered by the theorem. For a given order $n$, the block list below highlights the unique block containing the two selected points.

```{anywidget} ./widgets/blocks.mjs
:css: ./widgets/blocks.css
{}
```

## Previous results

At $n=6$ the six points form a single block. Among the orders satisfying the divisibility conditions, Fisher's inequality rules out 16 and 21. A system on 36 points would be an affine plane of order six. Its projective completion is excluded by the Bruck–Ryser theorem [@bruck1949nonexistence]. @houghten2001there proved nonexistence at 46 by exhaustive search.

Theorem 3.1 of @abel2007pair established existence at every other admissible order with 29 possible exceptions. @banakh2026steiner constructed systems for two of them, 226 and 441, leaving 27 orders unresolved [@banakh2026linear, Remark 10.4].

## New constructions

:::{div}
:class: s26-file-links

We construct systems of orders [166](https://zenodo.org/api/records/24417862/files/S-2-6-166.txt/content), [231](https://zenodo.org/api/records/24417862/files/S-2-6-231.txt/content), [256](https://zenodo.org/api/records/24417862/files/S-2-6-256.txt/content), [261](https://zenodo.org/api/records/24417862/files/S-2-6-261.txt/content), [286](https://zenodo.org/api/records/24417862/files/S-2-6-286.txt/content), [316](https://zenodo.org/api/records/24417862/files/S-2-6-316.txt/content), [321](https://zenodo.org/api/records/24417862/files/S-2-6-321.txt/content), [346](https://zenodo.org/api/records/24417862/files/S-2-6-346.txt/content), [351](https://zenodo.org/api/records/24417862/files/S-2-6-351.txt/content), [376](https://zenodo.org/api/records/24417862/files/S-2-6-376.txt/content), [406](https://zenodo.org/api/records/24417862/files/S-2-6-406.txt/content), [411](https://zenodo.org/api/records/24417862/files/S-2-6-411.txt/content), [436](https://zenodo.org/api/records/24417862/files/S-2-6-436.txt/content), [471](https://zenodo.org/api/records/24417862/files/S-2-6-471.txt/content), [501](https://zenodo.org/api/records/24417862/files/S-2-6-501.txt/content), [561](https://zenodo.org/api/records/24417862/files/S-2-6-561.txt/content), [591](https://zenodo.org/api/records/24417862/files/S-2-6-591.txt/content), [616](https://zenodo.org/api/records/24417862/files/S-2-6-616.txt/content), [646](https://zenodo.org/api/records/24417862/files/S-2-6-646.txt/content), [651](https://zenodo.org/api/records/24417862/files/S-2-6-651.txt/content), [676](https://zenodo.org/api/records/24417862/files/S-2-6-676.txt/content), [771](https://zenodo.org/api/records/24417862/files/S-2-6-771.txt/content), [796](https://zenodo.org/api/records/24417862/files/S-2-6-796.txt/content), and [801](https://zenodo.org/api/records/24417862/files/S-2-6-801.txt/content). This leaves only the orders 51, 61, and 81 open.
Each linked file gives one block per line, with points numbered from $0$ to $n-1$.

:::

The Lean proof proceeds by strong induction on $n$, using 118 finite designs, a product construction, and Wilson's weighting construction [@wilson1972composition, Theorem 11.2]. For each finite design the kernel checks that every block contains six points and every pair of distinct points lies in only one block.

```{literalinclude} ../../lean/Lemmata/SteinerSixSpectrum/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/steiner-six-spectrum.md
```
