---
title: Self-implication
---

```{include} ../_generated/provenance/self-implication.md
```

The smallest theorem worth stating, used here to show how an entry is put together.

```{prf:theorem} Self-implication
:label: thm-self-implication

For every proposition $P$, we have $P \to P$.
```

```{prf:proof}
Assume $P$. Then $P$ holds, which is what we had to show.
```

The formal statement and proof, included verbatim from the Lean library:

```{literalinclude} ../../lean/Lemmata/SelfImplication/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/self-implication.md
```
