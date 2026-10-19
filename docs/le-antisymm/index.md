---
title: Antisymmetry of order
---

```{include} ../_generated/provenance/le-antisymm.md
```

What separates a partial order from a mere preorder: elements cannot sit below each
other without being equal. Transitivity, the other half of the axioms, is
[composition of implications](#cor-implication-composition-le) in disguise.

```{prf:theorem} Antisymmetry
:label: thm-le-antisymm

Let $(P, \le)$ be a partial order and $a, b \in P$. If $a \le b$ and $b \le a$, then $a = b$.
```

```{prf:proof}
This is the antisymmetry axiom of a partial order.
```

```{prf:corollary} Equality from order
:label: cor-le-antisymm-eq-iff

In a partial order, $a = b \iff (a \le b \wedge b \le a)$.
```

```{prf:proof}
If $a = b$, both inequalities hold by reflexivity. The converse is
[](#thm-le-antisymm).
```

```{literalinclude} ../../lean/Lemmata/LeAntisymm/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/le-antisymm.md
```
