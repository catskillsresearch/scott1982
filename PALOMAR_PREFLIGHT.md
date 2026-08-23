# Palomar preflight

Mechanical checks before a Palomar submission. Style notes live in
`docs/PALOMAR_STYLE.md` (copied from the `scott1972` / `cardb` pattern).

```bash
scripts/palomar_preflight.sh
```

The script rejects project-local imports in `Challenge.lean`, validates
`comparator.json`, builds the Lake targets, compares Challenge vs Solution
types and locked definition bodies, rejects `sorry` in Solution sources,
audits theorem axioms against `permitted_axioms`, and runs `git diff --check`.
