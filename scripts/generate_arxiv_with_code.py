#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact).

Follows the scott1972 appendix convention: one markdown heading per Lean file
(demoted to a LaTeX ``\\subsection`` by ``build_arxiv_tex.py``), with the
verbatim source in a fenced ``lean`` block.
"""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Optional role labels for the appendix index table (keyed by repo-relative path).
# Files not listed here still appear; the Role cell falls back to the path stem.
FILE_ROLES: dict[str, str] = {
    "Scott1982.lean": "Root import graph",
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
    """Drop arxiv.md's GitHub-link Lean Code index; the appendix replaces it."""
    markers = ("\n## Lean Code\n", "\n## Lean Code\r\n")
    for marker in markers:
        idx = body.find(marker)
        if idx != -1:
            return body[:idx].rstrip() + "\n"
    if body.startswith("## Lean Code\n"):
        return ""
    return body


def lean_files_from_root() -> list[str]:
    """All library `.lean` files in `Scott1982.lean` import order, plus the root module."""
    root_mod = ROOT / "Scott1982.lean"
    files = ["Scott1982.lean"]
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


def sanitize_fence_content(content: str) -> str:
    # Nested ``` in docstrings would break markdown fences in arxiv_with_code.md.
    return content.replace("```", "'''")


def role_for(path: str) -> str:
    if path in FILE_ROLES:
        return FILE_ROLES[path]
    name = Path(path).stem
    if name.startswith("Factoid"):
        return "Factoid"
    if name.startswith("Definition"):
        return "Definition"
    if name.startswith("Theorem") or name.startswith("Lemma"):
        return "Theorem / Lemma"
    if name.startswith("Proposition"):
        return "Proposition"
    if name in {
        "InfoSys",
        "Approximable",
        "Product",
        "Sum",
        "FunctionSpace",
        "Fixpoint",
        "DomainEquation",
        "Constructive",
    }:
        return "Core infrastructure"
    return name


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = strip_lean_code_section(narrative_body(arxiv))
    files = lean_files_from_root()

    total_lines = 0
    file_line_counts: list[tuple[str, int]] = []
    for f in files:
        n = len((ROOT / f).read_text(encoding="utf-8").splitlines())
        file_line_counts.append((f, n))
        total_lines += n

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
        f"*Generated {date.today().isoformat()} from `arxiv.md` and {len(files)} library "
        f"`.lean` files ({total_lines} lines) in `Scott1982.lean` import order.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---` and the GitHub-link "
        "**Lean Code** index). This file appends **Appendix: Complete Lean source** "
        "with one subsection per file.\n\n"
    )
    parts.append("---\n\n")
    parts.append("# Narrative + Lean source (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append("| Role | File | Lines |\n")
    parts.append("| --- | --- | ---: |\n")
    for f, n in file_line_counts:
        parts.append(f"| {role_for(f)} | `{f}` | {n} |\n")
    parts.append(
        f"\n**Total:** {len(files)} files, {total_lines} lines of Lean.\n\n"
        "Files appear in `Scott1982.lean` import order. "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )

    for f, n in file_line_counts:
        content = sanitize_fence_content((ROOT / f).read_text(encoding="utf-8").rstrip()) + "\n"
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"Wrote {out} ({len(out.read_text(encoding='utf-8').splitlines())} lines)")


if __name__ == "__main__":
    main()
