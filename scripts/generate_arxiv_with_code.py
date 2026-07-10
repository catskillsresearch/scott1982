#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Library files in dependency order (matches Scott1982.lean import order).
FILES = [
    "Scott1982.lean",
    "Scott1982/Constructive.lean",
    "Scott1982/InfoSys.lean",
    "Scott1982/Definition22.lean",
    "Scott1982/Proposition23.lean",
    "Scott1982/Factoid24.lean",
    "Scott1982/Factoid25.lean",
    "Scott1982/Factoid26.lean",
    "Scott1982/Factoid32.lean",
    "Scott1982/Factoid33.lean",
    "Scott1982/Factoid34.lean",
    "Scott1982/Factoid35.lean",
    "Scott1982/Factoid36.lean",
    "Scott1982/Factoid41.lean",
    "Scott1982/Approximable.lean",
    "Scott1982/Proposition53.lean",
    "Scott1982/Proposition54.lean",
    "Scott1982/Proposition55.lean",
    "Scott1982/Proposition56.lean",
    "Scott1982/Product.lean",
    "Scott1982/Sum.lean",
    "Scott1982/FunctionSpace.lean",
    "Scott1982/Fixpoint.lean",
    "Scott1982/DomainEquation.lean",
]

FILE_ROLES: dict[str, str] = {
    "Scott1982.lean": "Root import graph",
    "Scott1982/Constructive.lean": "Choice-free Finset prelude",
    "Scott1982/InfoSys.lean": "Def 2.1 + Def 3.1 (Element)",
    "Scott1982/Definition22.lean": "Def 2.2 EntSet",
    "Scott1982/Proposition23.lean": "Prop 2.3",
    "Scott1982/Factoid24.lean": "Factoid 2.4 ℕ lower-bound example",
    "Scott1982/Factoid25.lean": "Factoid 2.5 interval example",
    "Scott1982/Factoid26.lean": "Factoid 2.6 partial-function example",
    "Scott1982/Factoid32.lean": "Δ ∈ every element",
    "Scott1982/Factoid33.lean": "⊥ least",
    "Scott1982/Factoid34.lean": "top / Tot",
    "Scott1982/Factoid35.lean": "finite closure ū",
    "Scott1982/Factoid36.lean": "x = ⋃{ū | u ⊆ x}",
    "Scott1982/Factoid41.lean": "inf-semilattice under ∩",
    "Scott1982/Approximable.lean": "Def 5.1–5.2",
    "Scott1982/Proposition53.lean": "Prop 5.3(ii)(iii)(v), singleton reduction",
    "Scott1982/Proposition54.lean": "identity map",
    "Scott1982/Proposition55.lean": "composition",
    "Scott1982/Proposition56.lean": "constant maps",
    "Scott1982/Product.lean": "Def 6.1 productSystem",
    "Scott1982/Sum.lean": "Def 6.3 / Prop 6.4 (skeleton)",
    "Scott1982/FunctionSpace.lean": "Def 7.1 / Thm 7.2 (skeleton)",
    "Scott1982/Fixpoint.lean": "Thm 7.3 / Prop 7.4 (skeleton)",
    "Scott1982/DomainEquation.lean": "§8 domain equations (skeleton)",
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


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text()
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and all library "
        "`.lean` files in dependency order (`Scott1982.lean`).*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Complete Lean source** with every line "
        "of the formalization inlined below. Acknowledgments are injected later when "
        "building `arxiv.tex`.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body (Acknowledgments added at tex build) |\n")
    parts.append("| **Appendix** | Lean source index (in narrative) + complete Lean 4 source |\n\n")
    parts.append("### Complete Lean source — file index\n\n")

    total_lines = 0
    for f in FILES:
        n = len((ROOT / f).read_text().splitlines())
        total_lines += n
        parts.append(f"- [`{f}`](#{f.replace('/', '').replace('.', '').lower()}) — {n} lines\n")

    parts.append(f"\n**Total:** {len(FILES)} files, {total_lines} lines of Lean.\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append("| Role | File |\n")
    parts.append("| --- | --- |\n")
    for f in FILES:
        parts.append(f"| {FILE_ROLES[f]} | `{f}` |\n")
    parts.append(
        "\nPrimary source (OCR): [`sources/Domains_for_Denotational_Semantics.md`]"
        "(sources/Domains_for_Denotational_Semantics.md) — transcription of **[Sco82]**.\n\n"
    )
    parts.append(
        "Files appear in `Scott1982.lean` import order. "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )

    for f in FILES:
        content = (ROOT / f).read_text().rstrip() + "\n"
        # Nested ``` in docstrings would break markdown lean fences in arxiv_with_code.md.
        content = content.replace("```", "'''")
        n = len(content.splitlines())
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"Wrote {out} ({len(out.read_text().splitlines())} lines)")


if __name__ == "__main__":
    main()
