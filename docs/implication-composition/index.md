---
title: Composition of implications
---

```{include} ../_generated/provenance/implication-composition.md
```

Implications chain. This is the archive's worked example: it shows the pieces an entry
can use — numbered results, a diagram, a widget, a Mathlib corollary — on a result small
enough to read at a glance.

```{prf:theorem} Composition
:label: thm-implication-composition

Let $P$, $Q$, $R$ be propositions. If $P \to Q$ and $Q \to R$, then $P \to R$.
```

```{prf:proof}
Assume $P$. From $P \to Q$ we get $Q$, and from $Q \to R$ we get $R$.
```

```{mermaid}
flowchart LR
  P -->|"h₁ : P → Q"| Q -->|"h₂ : Q → R"| R
  P -.->|"composition"| R
```

Composing with self-implication ($P \to P$) on either side changes nothing:

```{literalinclude} ../../lean/Lemmata/ImplicationComposition/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{prf:corollary} Transitivity of order
:label: cor-implication-composition-le

In a preorder, $a \le b$ and $b \le c$ give $a \le c$:

$$
a \le b \;\wedge\; b \le c \;\Longrightarrow\; a \le c .
$$ (eq-implication-composition-le)
```

Try it: pick which hypotheses hold, and see whether $R$ follows.

```{anywidget} ./widgets/chain.mjs
:css: ./widgets/chain.css
{"p": true, "pq": true, "qr": true}
```

```{include} ../_generated/verification/implication-composition.md
```
