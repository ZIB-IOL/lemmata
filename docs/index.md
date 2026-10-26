---
numbering:
  headings: false
title: Lemmata Repository
---

# Lemmata Repository

A living archive of mathematics. Every entry is written twice: once for people, in the
prose you are reading, and once for Lean, in a formal proof that the kernel has checked.

Lemmata is a home for **formalized results that are worth sharing before, or without, a
full paper**: lemmas and constructions that may never become a paper of their own but are
still useful to others, and results at a stage before a preprint — a way to disseminate
them early, with the Lean proof as evidence. It is equally a place to **archive the
formalization of results from a paper**, preprint or published, linked to it, so the
proofs have a permanent, citable home next to the text. Entries are self-contained, and
each has a stable identifier to cite.

Entries are web pages rather than papers. They are written in MyST Markdown and rendered
as HTML with KaTeX, so an entry can use what fits the mathematics — numbered results,
diagrams, interactive widgets — instead of a fixed paper layout. We chose HTML on purpose:
almost any information can be represented in it well, more richly than in a static
document [@shihipar2026html].

The repository is also built to be read by machines, and by language models in
particular. [`/llms.txt`](https://lemmata.iol.berlin/llms.txt) is a plain-text overview of
every entry with its identifier and status;
[`/lemmata.json`](https://lemmata.iol.berlin/lemmata.json) is a machine-readable index with
every exported Lean declaration, its verification status and axioms, and a BibTeX entry.
Every entry links the Lean source of each result, and its page can be downloaded as
Markdown. Coding agents that want to contribute follow AGENTS.md (linked below), the
contribution procedure written for them.

```{include} _generated/contributing.md
```

```{include} _generated/catalog.md
```

## What "checked" means here

A **kernel-checked** result is one whose formal statement compiles and was accepted by
Lean's kernel, using only the standard axioms. That the English statement means the same
as the Lean statement is checked by human review. [Read the full definition](checked.md).

For what "verified in Lean" does and does not establish, and what a reader should still
check, we recommend the essay by @spiegel2026trust.
