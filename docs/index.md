---
title: Lemmata
---

# Lemmata

A living archive of mathematics. Every entry is written twice: once for people, in the
prose you are reading, and once for Lean, in a formal proof that the kernel has checked.

Lemmata is a home for **formalized results that are worth sharing before, or without, a
full paper**: lemmas and constructions that may never become a paper of their own but are
still useful to others, and results at a stage before a preprint — a way to disseminate
them early, with the Lean proof as evidence. Entries are short and self-contained, and
each has a stable identifier to cite.

Entries are web pages rather than papers. They are written in MyST Markdown and rendered
as HTML with KaTeX, so an entry can use what fits the mathematics — numbered results,
diagrams, interactive widgets — instead of a fixed paper layout. We chose HTML on purpose:
almost any information can be represented in it well, more richly than in a static
document [@shihipar2026html]. [Lax](https://laxarchive.org/about.html) links Lean to
papers, which it keeps as the primary way of explaining a result; Lemmata is for the
results that come before, or alongside, a paper.

```{include} _generated/contributing.md
```

```{include} _generated/catalog.md
```

## What "checked" means here

A **kernel-checked** result is one whose formal statement compiles and was accepted by
Lean's kernel, using only the standard axioms. That the English statement means the same
as the Lean statement is checked by human review. [Read the full definition](checked.md).
