[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1982/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1982/actions/workflows/build.yml)
# scott1982

Lean 4 formalization of Dana Scott's **1982** *Domains for Denotational Semantics*
(ICALP) — information systems (constructive presentation).

Includes a choice-free `Finset` prelude (`Scott1982.Constructive`) and `Scott1982.InfoSys`.

Standalone package — no dependency on the 1972/1980 formalizations. Cross-presentation
equivalence theorems live in [`scott_models`](../scott_models); this repo is packaged for
[Palomar](https://palomar-registry.org/about) on its own (see `PROVENANCE.md`).
The compared Palomar claim is **only** the first sentence of Theorem 7.2
(approximable maps `A → B` are the elements of `|A → B|`), not the `apply` /
`curry` clauses and not the whole paper.

## Files (Palomar)

| File | Role |
|---|---|
| `arxiv.md` | Formalization narrative and theorem inventory |
| `sources/Domains_for_Denotational_Semantics.pdf` | Scott 1982 source paper (repository copy) |
| `Scott1982/` | Sorry-free formalization of the paper |
| `Challenge.lean` | Palomar statement of record: Theorem 7.2, first sentence |
| `Solution.lean` | Palomar solution module: imports `Scott1982/*` proofs |
| `comparator.json` | Comparator config for the compared theorem and definitions |
| `formalization.yaml` | Palomar / formalization.yaml v0.4 metadata |
| `PROVENANCE.md` | Standalone Palomar submission; relation to siblings |

## Build

```bash
lake exe cache get
lake build
```

`lake build` typechecks `Scott1982`, `Challenge.lean`, and `Solution.lean`. Before a
Palomar submission, run:

```bash
bash scripts/palomar_preflight.sh
```

Pinned: Lean / mathlib **v4.30.0** (`lean-toolchain`).
`Challenge.lean` imports Mathlib only and restates the choice-free `Finset`
union so Definition 7.1 can be stated without `Classical.choice` and without
a project-local import. The compared theorem is intended to use `propext` and
`Quot.sound` only. Token types are assumed to have `DecidableEq`.
