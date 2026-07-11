#!/usr/bin/env python3
"""Optional review artifact: expand Lean GitHub links from arxiv.md → arxiv_with_code.md.

The arXiv pipeline (``scripts/build_arxiv_tex.py``) reads ``arxiv.md`` directly and keeps
the Lean Code appendix as GitHub hyperlinks only (scott1980 style). This script is for
local review copies that inline sources; it is **not** part of the arXiv build.
"""

from __future__ import annotations

from datetime import date
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent

LEAN_CODE_LINK_RE = re.compile(
    r"^\* \[([^\]]+\.lean)\]\("
    r"https://github\.com/[^/]+/[^/]+/blob/[^/]+/"
    r"([^)]+)\)"
    r"(?:[ \t]+([—–-].*))?[ \t]*$",
    re.MULTILINE,
)


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


def expand_lean_links(text: str) -> str:
    """Replace Lean Code GitHub bullets with inlined ```lean fences."""
    marker = "## Lean Code"
    pos = text.find(marker)
    if pos == -1:
        raise RuntimeError("missing ## Lean Code in arxiv.md")
    head, tail = text[:pos], text[pos:]

    def repl(match: re.Match[str]) -> str:
        relpath = match.group(2)
        path = ROOT / relpath
        if not path.is_file():
            raise FileNotFoundError(f"Lean file not found for link: {relpath}")
        content = path.read_text(encoding="utf-8").rstrip() + "\n"
        content = content.replace("```", "'''")
        n = len(content.splitlines())
        return (
            f"* **{match.group(1)}** (`{relpath}`) — {n} lines\n\n"
            f"```lean\n{content}```\n"
        )

    new_tail, count = LEAN_CODE_LINK_RE.subn(repl, tail)
    if count == 0:
        raise RuntimeError(
            "No Lean Code GitHub blob links found. Expected bullets like "
            "`* [InfoSys.lean](https://github.com/.../blob/main/Scott1982/InfoSys.lean)`."
        )
    return head + new_tail


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = expand_lean_links(narrative_body(arxiv))

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: optional review copy; arXiv build uses arxiv.md directly -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents / not for arXiv.** Inventory lives in "
        "[`arxiv.md`](arxiv.md). The arXiv pipeline keeps Lean Code as GitHub links only. "
        "Regenerate this review copy with `scripts/generate_arxiv_with_code.sh`.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` Lean Code hyperlinks "
        "(sources inlined for local review).*\n\n"
    )
    parts.append("---\n\n")
    parts.append(body)
    parts.append("\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts), encoding="utf-8")
    print(f"Wrote {out} ({len(out.read_text(encoding='utf-8').splitlines())} lines)")


if __name__ == "__main__":
    main()
