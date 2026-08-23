# Provenance

This repository is a standalone Lean 4 formalization of Dana Scott's 1982
ICALP paper *Domains for Denotational Semantics*. It is not a thin wrapper
and not a reimplementation of an independent formalization.

Dana Scott did not participate in, review, or endorse this formalization.
The formalization was produced by Lars Warren Ericson without input from
Scott. The source paper is cited as literature only.

Cross-presentation equivalence theorems for Scott's 1972 / 1980 / 1982
material live in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models).
**This repository is submitted to Palomar on its own**, for the 1982
paper alone, following the same Challenge / Solution pattern as
[`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972)
and
[`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980).

The compared Palomar claim is **Theorem 7.2, first sentence**: if `A` and
`B` are information systems, then so is `A → B`, and the approximable
mappings `A → B` are exactly the elements of `|A → B|`. The remaining
`apply` / `curry` clauses of Theorem 7.2 are proved in the library and
are not Comparator targets. The §§1–8 development lives in `Scott1982/*`.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
