#!/usr/bin/env python3
"""Expand arxiv.md → arxiv_with_code.md with a Lean-module appendix.

Each library file is a subsection whose title is a hyperlink to the Palomar
archive snapshot, followed by a brief description. The Lean source itself is
not copied.
"""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

PALOMAR_BLOB = (
    "https://github.com/PalomarArchive/catskillsresearch--scott1982--ca9aa6e0a302"
    "/blob/d3221eec09505aa75e1b818aabc73f1f04339bdc"
)

FILE_DESCRIPTIONS: dict[str, str] = {
    "Challenge.lean": (
        "Palomar statement of record for the first sentence of Theorem 7.2. "
        "Imports Mathlib only and restates the locked definitions with deliberate "
        "`sorry`s."
    ),
    "Solution.lean": (
        "Palomar solution module. Imports the sorry-free Theorem 7.2 development "
        "so compared names and types match the Challenge."
    ),
    "Scott1982.lean": (
        "Root import graph. Re-exports every library module in dependency order."
    ),
    "Scott1982/Constructive.lean": (
        "Choice-free Finset prelude: `funion` (`∪'`), insert commutativity, and "
        "decidable Finset equality, avoiding Mathlib's choice-tainted union."
    ),
    "Scott1982/InfoSys.lean": (
        "Definition 2.1 information systems and Definition 3.1 elements, with "
        "the carrier-inclusion partial order."
    ),
    "Scott1982/Definition22.lean": (
        "Definition 2.2: set-level entailment `u ⊢ v`."
    ),
    "Scott1982/Proposition23.lean": (
        "Proposition 2.3: elementary properties of set-level entailment."
    ),
    "Scott1982/Factoid24.lean": (
        "Factoid 2.4: first example — lower-bound information system on ℕ."
    ),
    "Scott1982/Factoid25.lean": (
        "Factoid 2.5: second example — open intervals plus `(0, ∞)`."
    ),
    "Scott1982/Factoid26.lean": (
        "Factoid 2.6: third example — partial-function graphs plus `Δ`."
    ),
    "Scott1982/Factoid32.lean": (
        "Factoid 3.2: every element contains `Δ`."
    ),
    "Scott1982/Factoid33.lean": (
        "Factoid 3.3: the bottom element `⊥`."
    ),
    "Scott1982/Factoid34.lean": (
        "Factoid 3.4: top element and total elements."
    ),
    "Scott1982/Factoid35.lean": (
        "Factoid 3.5: finite elements as entailment closures `ū`."
    ),
    "Scott1982/Factoid36.lean": (
        "Factoid 3.6: every element is the directed union of its finite "
        "approximations."
    ),
    "Scott1982/Factoid41.lean": (
        "Factoid 4.1: `|A|` is an inf-semilattice under intersection."
    ),
    "Scott1982/Factoid42.lean": (
        "Factoid 4.2: conditional completeness for meets."
    ),
    "Scott1982/Factoid43.lean": (
        "Factoid 4.3: consistent joins."
    ),
    "Scott1982/Factoid44.lean": (
        "Factoid 4.4: directed (and chain) unions are elements; cpo structure."
    ),
    "Scott1982/Factoid45.lean": (
        "Factoid 4.5: algebraicity via compact finite elements."
    ),
    "Scott1982/Factoid46.lean": (
        "Factoid 4.6: Scott topology and continuous maps."
    ),
    "Scott1982/Approximable.lean": (
        "Definitions 5.1–5.2: approximable mappings and `toElement`."
    ),
    "Scott1982/Proposition53.lean": (
        "Proposition 5.3: images, order, and the closure bridge."
    ),
    "Scott1982/Proposition54.lean": (
        "Proposition 5.4: the identity approximable mapping."
    ),
    "Scott1982/Proposition55.lean": (
        "Proposition 5.5: composition of approximable mappings."
    ),
    "Scott1982/Proposition56.lean": (
        "Proposition 5.6: constant approximable mappings."
    ),
    "Scott1982/Product.lean": (
        "Definition 6.1: product information system `A × B`."
    ),
    "Scott1982/Proposition62.lean": (
        "Proposition 6.2: product projections and pairing."
    ),
    "Scott1982/Sum.lean": (
        "Definition 6.3: separated sum `A + B`."
    ),
    "Scott1982/Proposition64.lean": (
        "Proposition 6.4: sum injections and copairing."
    ),
    "Scott1982/Factoid65.lean": (
        "Factoid 6.5: the unit domain (empty product)."
    ),
    "Scott1982/FunctionSpace.lean": (
        "Definition 7.1: the function-space information system `A → B`."
    ),
    "Scott1982/Theorem72.lean": (
        "Theorem 7.2: approximable maps are the elements of `|A → B|`; apply "
        "and curry."
    ),
    "Scott1982/Fixpoint.lean": (
        "Theorem 7.3: unique approximable least fixed-point operator `fix`."
    ),
    "Scott1982/Proposition74.lean": (
        "Proposition 7.4: Plotkin’s equational characterization of `fix`."
    ),
    "Scott1982/Factoid75.lean": (
        "Factoid 7.5: strict mappings, `strictify`, BOOL, and the conditional."
    ),
    "Scott1982/Factoid76.lean": (
        "Factoid 7.6: combinators as approximable operators (`const`, `pair`, "
        "`comp`)."
    ),
    "Scott1982/Factoid77.lean": (
        "Factoid 7.7: cartesian closed packaging as a Mathlib category."
    ),
    "Scott1982/Factoid81.lean": (
        "Factoid 8.1: tree / S-expression domain `T ≅ A + (T × T)`."
    ),
    "Scott1982/Factoid82.lean": (
        "Factoid 8.2: λ-calculus model `D ≅ A + (D → D)`."
    ),
    "Scott1982/Factoid83.lean": (
        "Factoid 8.3: universal domain via `V` (with top) and `U` (top removed)."
    ),
    "Scott1982/Factoid84.lean": (
        "Factoid 8.4: Scott’s sketch of a domain of domains on the powerset `P`."
    ),
    "Scott1982/DomainEquation.lean": (
        "Section 8 re-export of the Factoid 8.1–8.2 constructions."
    ),
}


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 1982"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def strip_lean_code_section(body: str) -> str:
    """Drop arxiv.md's Lean Code index; the appendix replaces it."""
    markers = ("\n## Lean Code\n", "\n## Lean Code\r\n")
    for marker in markers:
        idx = body.find(marker)
        if idx != -1:
            return body[:idx].rstrip() + "\n"
    if body.startswith("## Lean Code\n"):
        return ""
    return body


def lean_files_from_root() -> list[str]:
    """Palomar packaging files, then library modules in `Scott1982.lean` order."""
    root_mod = ROOT / "Scott1982.lean"
    files = ["Challenge.lean", "Solution.lean", "Scott1982.lean"]
    for line in root_mod.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line.startswith("import "):
            continue
        mod = line.removeprefix("import ").strip()
        if not mod.startswith("Scott1982."):
            continue
        rel = mod.replace(".", "/") + ".lean"
        files.append(rel)
    return files


def palomar_url(path: str) -> str:
    return f"{PALOMAR_BLOB}/{path}"


def description_for(path: str) -> str:
    if path in FILE_DESCRIPTIONS:
        return FILE_DESCRIPTIONS[path]
    return f"Lean module `{path}`."


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = strip_lean_code_section(narrative_body(arxiv))
    files = lean_files_from_root()

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + Lean module index\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md`.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and {len(files)} Lean "
        f"modules linked to the Palomar archive snapshot.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---` and the GitHub-link "
        "**Lean Code** index). This file appends **Appendix: Lean source** "
        "with one subsection per file: a Palomar hyperlink and a brief description, "
        "not a verbatim copy of the Lean.\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative + Lean source (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Lean source\n\n")
    parts.append(
        "Lean modules in Palomar packaging order, then `Scott1982.lean` import "
        "order. Each subsection title links to the registered Palomar archive "
        "snapshot "
        "[`d3221eec09505aa75e1b818aabc73f1f04339bdc`]("
        "https://github.com/PalomarArchive/catskillsresearch--scott1982--ca9aa6e0a302"
        "/tree/d3221eec09505aa75e1b818aabc73f1f04339bdc). "
        "The Lean text is not reproduced here.\n\n"
    )

    for f in files:
        url = palomar_url(f)
        parts.append(f"## [`{f}`]({url})\n\n")
        parts.append(f"{description_for(f)}\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"Wrote {out} ({len(out.read_text(encoding='utf-8').splitlines())} lines)")


if __name__ == "__main__":
    main()
