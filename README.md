[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1982/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1982/actions/workflows/build.yml)
# scott1982

Lean 4 formalization of Dana Scott's **1982** *Domains for Denotational Semantics*
(ICALP) — information systems (constructive presentation).

Includes a choice-free `Finset` prelude (`Scott1982.Constructive`) and `Scott1982.InfoSys`.

Standalone package. Part IV equivalence theorems live in [`scott_models`](../scott_models).

## Build

```bash
lake exe cache get
lake build Scott1982
```

Pinned: Lean / mathlib **v4.30.0** (`lean-toolchain`).
