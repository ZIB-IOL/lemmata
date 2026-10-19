---
title: Lemmata
---

# Lemmata

A living archive of mathematics. Every entry is written twice: once for people, in the
prose you are reading, and once for Lean, in a formal proof that the kernel has checked.
New entries arrive by merge request; the site rebuilds itself from `main` within minutes.
The [build status](https://lemmata.iol.berlin/_status) shows which version is live and,
for a commit that was not published, why.

```{include} _generated/catalog.md
```

## What "checked" means here

A **checked** badge says three things, all established by machinery rather than by the
author: the formal declaration exists and compiles, Lean's kernel accepted it, and it
depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The formal
library builds on Mathlib [@mathlib2020].

It does **not** say that the English statement means the same as the Lean statement.
That correspondence is checked by human review, and every page links to the exact formal
source it was reviewed against.
