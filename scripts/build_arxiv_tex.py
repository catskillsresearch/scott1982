#!/usr/bin/env python3
r"""Convert arxiv_with_code.md to arxiv.tex (PDF build).

Pipeline:
  1. Drop the GitHub-only navigation preamble from ``arxiv_with_code.md``.
  2. Lift the `## Abstract` section into a LaTeX \begin{abstract}.
  3. Demote Appendix Lean-file headings so each module is a ``\\subsection``
     (scott1972 convention), then insert \\appendix before Complete Lean source.
  4. Strip manual section numbers so LaTeX does the numbering.
  5. Replace fenced Lean/math/bash with \\lstinputlisting blocks; render mermaid to PDF.
  6. Inject AI model-card acknowledgements; pandoc -> LaTeX; splice placeholders.
  7. Emit a single ``arxiv.tex`` for one-shot latexmk (LuaLaTeX locally).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from ai_model_cards import inject_model_cards
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
LISTING_CHUNK_LINES = 400
_WRITTEN_LISTINGS: set[Path] = set()

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/scott1982"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def render_mermaid(code: str, idx: int) -> str:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    pdf_path = FIGURES_DIR / f"figure-{idx:03d}.pdf"
    code_stripped = code.strip() + "\n"
    if (
        mmd_path.is_file()
        and pdf_path.is_file()
        and mmd_path.read_text(encoding="utf-8") == code_stripped
    ):
        return pdf_path.relative_to(ROOT).as_posix()
    mmd_path.write_text(code_stripped, encoding="utf-8")

    mmdc = shutil.which("mmdc")
    if not mmdc:
        raise RuntimeError(
            "mermaid-cli (mmdc) not found; install with "
            "`npm install -g @mermaid-js/mermaid-cli`"
        )
    env = os.environ.copy()
    chrome = find_chrome()
    if chrome:
        env["PUPPETEER_EXECUTABLE_PATH"] = chrome
    cmd = [mmdc, "-i", str(mmd_path), "-o", str(pdf_path), "--pdfFit", "-b", "transparent"]
    if PUPPETEER_CONFIG.is_file():
        cmd += ["-p", str(PUPPETEER_CONFIG)]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    if proc.returncode != 0 or not pdf_path.is_file():
        sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
        raise RuntimeError(f"mmdc failed to render figure {idx}")
    return pdf_path.relative_to(ROOT).as_posix()


def extract_title() -> str:
    first = (ROOT / "arxiv.md").read_text(encoding="utf-8").splitlines()[0]
    title = first[2:].strip() if first.startswith("# ") else first.strip()
    title = re.sub(r"\*([^*]+)\*", r"\\emph{\1}", title)
    return title


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative + Lean source (from arxiv.md)"
# After normalize_appendix_headings: `### Scott1982/...File.lean` precedes each fence.
LEAN_FILE_HEADING_RE = re.compile(
    r"^###\s+(Scott1982(?:\.lean|/[\w./-]+\.lean))\s*$"
)
APPENDIX_HEADING_RE = re.compile(
    r"^##\s+Appendix\s+[A-Z]\s*[-\u2013\u2014]+\s*(.+)$", re.MULTILINE
)
COMPOSER_APPENDIX_START = re.compile(
    r"^##\s+(?:Appendix\s+[AB]\s*[-\u2013\u2014]+\s*)?"
    r"(?:Exercise 7\.22 Composer (?:autorun|playbook)|Appendix\s+[AB]\s*[-\u2013\u2014])",
    re.MULTILINE,
)
# ASCII fallbacks for combining-mark sequences and emoji that `\newunicodechar` cannot
# handle cleanly (accents stack backwards in LaTeX; emoji have no single-glyph textcomp
# equivalent worth a new package dependency). Order matters: longer sequences first.
PROSE_ASCII_FALLBACKS: tuple[tuple[str, str], ...] = (
    ("\u26a0\ufe0f", "Warning:"),  # WARNING SIGN + VARIATION SELECTOR-16
    ("\u26a0", "Warning:"),  # bare WARNING SIGN
    ("w\u20d7", "w-vec"),  # w + COMBINING RIGHT ARROW ABOVE
    ("\u03c3\u20d7", "sigma-vec"),  # sigma + COMBINING RIGHT ARROW ABOVE
    ("\U0001d4af", "T"),  # MATHEMATICAL SCRIPT CAPITAL T (𝒯) — prose only; pdfLaTeX-safe
    ("f\u0302", "f-hat"),  # f + COMBINING CIRCUMFLEX ACCENT
    ("\u039b\u0302", "Lambda-hat"),  # Lambda + COMBINING CIRCUMFLEX ACCENT
    ("\u2705", r"\ensuremath{\checkmark}"),  # WHITE HEAVY CHECK MARK
    ("\u2611", r"\ensuremath{\checkmark}"),  # BALLOT BOX WITH CHECK
    ("\u2610", "[ ]"),  # BALLOT BOX (Composer checklist unchecked)
)


def apply_prose_ascii_fallbacks(text: str) -> str:
    for src, dst in PROSE_ASCII_FALLBACKS:
        text = text.replace(src, dst)
    # Remaining COMBINING RIGHT ARROW ABOVE (e.g. 1⃗, 01⃗) after explicit σ⃗/w⃗ rules.
    text = re.sub(r"(.)\u20d7", r"\1-vec", text)
    return text


def github_math_to_tex(text: str) -> str:
    return GITHUB_INLINE_MATH.sub(r"$\1$", text)


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    idx = text.find(NARRATIVE_MARKER)
    if idx == -1:
        return text
    return text[idx + len(NARRATIVE_MARKER) :].lstrip("\n")


def normalize_appendix_headings(text: str) -> str:
    """Match scott1972 heading demotion so each Lean file becomes a ``\\subsection``.

    ``# Appendix A: Complete Lean source`` → ``## Complete Lean source``
    (pandoc shift-1 → ``\\section``).

    ``## `Scott1982/...File.lean``` → ``### Scott1982/...File.lean``
    (pandoc shift-1 → ``\\subsection``).

    Also drop the redundant literal "Appendix X --" prefix from any Composer
    ``## Appendix A/B -- ...`` headings if present.
    """
    text = re.sub(
        r"^#\s+Appendix A: Complete Lean source\s*$",
        "## Complete Lean source",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"^##\s+`(Scott1982(?:\.lean|/[^`]+))`\s*$",
        r"### \1",
        text,
        flags=re.MULTILINE,
    )
    return APPENDIX_HEADING_RE.sub(lambda m: f"## {m.group(1)}", text)


def demote_inventory_headings(text: str) -> str:
    """Turn `#### Exercise 2.1` inventory rows into bold text, not LaTeX subsubsections.

    The chronological narrative has 300+ such headings; pdfLaTeX's subsubsection counter
    overflows at 255.

    A blank line must follow the bold text: pandoc's markdown reader (unlike CommonMark)
    does not let a bullet list interrupt a paragraph, so without it every immediately
    following `* **Mathematical Target:**` / `* **Lean File:**` / `* **Proof Notes:**`
    block renders as a run-on paragraph with literal `*` characters instead of a proper
    itemized list.
    """
    return re.sub(r"^#### (.+)$", r"**\1**\n", text, flags=re.MULTILINE)


def drop_composer_appendices(text: str) -> str:
    """Drop Exercise 7.22 Composer session docs if present as appendix sections."""
    m = COMPOSER_APPENDIX_START.search(text)
    if not m:
        return text
    return text[: m.start()].rstrip() + "\n"


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return "", text
    abstract_md = m.group(1).strip()
    body = text[: m.start()] + text[m.end() :]
    return abstract_md, body


def extract_mermaid_captions(text: str) -> list[str]:
    """Caption each ```mermaid block from the nearest preceding markdown heading."""
    captions: list[str] = []
    for m in re.finditer(r"^```mermaid\s*$", text, re.MULTILINE):
        prefix = text[: m.start()]
        heading = None
        for line in reversed(prefix.splitlines()):
            hm = re.match(r"^#{2,4}\s+(.+)$", line.strip())
            if hm:
                heading = hm.group(1).strip()
                break
        if heading and heading.startswith("Lecture "):
            captions.append(f"Lean module dependencies for {heading}.")
        elif heading and "chapter" in heading.lower():
            captions.append(heading.rstrip(".") + ".")
        elif heading:
            captions.append(f"{heading}.")
        else:
            captions.append(f"Module dependency diagram {len(captions) + 1}.")
    return captions


def figure_latex(rel_path: str, caption: str, label: str) -> str:
    return (
        "\\begin{figure}[htbp]\n"
        "\\centering\n"
        f"\\includegraphics[max width=\\linewidth,"
        f"max totalheight=0.85\\textheight,keepaspectratio]{{{rel_path}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n"
    )


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(code.rstrip("\n"))
    listing_path = LISTINGS_DIR / listing_name
    write_if_changed(listing_path, source + "\n")
    _WRITTEN_LISTINGS.add(listing_path.resolve())
    rel_path = listing_path.relative_to(ROOT).as_posix()
    return rel_path, (len(source.splitlines()) if source else 0)


def prune_stale_listings() -> None:
    if not LISTINGS_DIR.is_dir():
        return
    for path in LISTINGS_DIR.iterdir():
        if path.is_file() and path.resolve() not in _WRITTEN_LISTINGS:
            path.unlink()


def lean_block_latex(code: str, listing_name: str) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)

    parts: list[str] = []
    for first, last in ranges:
        if first == 1 and last == line_count:
            parts.append(
                "\\vspace{0.5\\baselineskip}\n"
                "\\noindent\\textcolor{green!40!black}{\\textbf{Lean 4 source}}"
                "\\par\\vspace{0.25\\baselineskip}\n"
                f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
                "\\vspace{0.5\\baselineskip}\n\n"
            )
        else:
            parts.append(
                f"\\noindent\\textcolor{{green!40!black}}{{\\textbf{{Lean 4 source "
                f"(lines {first}--{last})}}}}\\par\\vspace{{0.25\\baselineskip}}\n"
                f"\\lstinputlisting[style=leanbox,firstline={first},lastline={last}]"
                f"{{{rel_path}}}\n\n"
            )
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    """Map each ```lean fence to its module path from the preceding ``### path`` heading."""
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        prefix = text[:pos].rstrip("\n")
        module = None
        for line in reversed(prefix.splitlines()[-6:]):
            m = LEAN_FILE_HEADING_RE.match(line.strip())
            if m:
                module = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(text: str) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    mermaid_captions = extract_mermaid_captions(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0
    mermaid_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx, mermaid_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            placeholders[key] = lean_block_latex(body, safe_name)
            return f"\n\n{key}\n\n"
        if lang == "math":
            key = f"MATHINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            return f"\n\n{key}\n\n"
        if lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path = render_mermaid(body, mermaid_idx)
            caption = (
                mermaid_captions[mermaid_idx]
                if mermaid_idx < len(mermaid_captions)
                else f"Module dependency diagram {mermaid_idx + 1}"
            )
            slug = re.sub(r"[^a-z0-9]+", "-", caption.lower()).strip("-")[:48] or str(
                mermaid_idx + 1
            )
            label = f"fig:mermaid-{slug}"
            mermaid_idx += 1
            other_idx += 1
            placeholders[key] = figure_latex(rel_path, caption, label)
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{other_idx:03d}"
        rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
        other_idx += 1
        placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
        return f"\n\n{key}\n\n"

    converted = FENCE_RE.sub(repl, text)
    return converted, placeholders


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=none",
    ]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(
            rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+",
            r"\1",
            latex,
        )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean source index\}",
        "",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A: Complete Lean source\}",
        r"\\section{Complete Lean source}",
        latex,
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_appendix_command(latex: str) -> str:
    marker = r"\section{Complete Lean source}"
    if marker not in latex:
        raise RuntimeError(f"missing {marker!r} in LaTeX output")
    return latex.replace(marker, r"\appendix" + "\n" + marker, 1)


def insert_list_of_figures(latex: str) -> str:
    marker = r"\hypertarget{references}{%"
    if marker not in latex:
        raise RuntimeError(f"missing {marker!r} in LaTeX output")
    return latex.replace(marker, r"\listoffigures" + "\n\n" + marker, 1)


def build_document(preamble: str, title_page: str, body: str) -> str:
    return preamble + "\n\n" + title_page + "\n\n" + body + "\n\n\\end{document}\n"


def write_if_changed(path: Path, content: str) -> bool:
    """Write ``path`` only when content differs; return True if the file was updated."""
    if path.is_file() and path.read_text(encoding="utf-8") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def cleanup_abstract_latex(latex: str) -> str:
    """Keep the abstract LaTeX-safe: ASCII plus standard LaTeX escapes."""
    latex = latex.replace("\\pandocbounded{", "{")
    latex = latex.replace("\\textbf{{[}", "\\textbf{[")
    latex = latex.replace("\\texttt{{[}", "\\texttt{[")
    latex = latex.replace("{]}}", "]}")
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    return latex


def build_title_page(abstract_latex: str) -> str:
    return textwrap.dedent(
        f"""
        \\title{{\\textbf{{{TITLE}}}}}

        \\author[1]{{\\textbf{{{AUTHOR}}}}}
        \\affil[1]{{{COMPANY}}}
        \\affil[1]{{\\url{{{GITHUB_URL}}}}}
        \\affil[1]{{\\texttt{{{EMAIL}}}}}

        \\date{{\\today}}

        \\begin{{document}}

        \\maketitle

        \\begin{{center}}
          \\small
          \\textbf{{ORCID:}} {ORCID}
        \\end{{center}}

        \\begin{{abstract}}
        {abstract_latex.strip()}
        \\end{{abstract}}
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(
            f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first",
            file=sys.stderr,
        )
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    for d in (LISTINGS_DIR, FIGURES_DIR):
        d.mkdir(parents=True, exist_ok=True)
    _WRITTEN_LISTINGS.clear()

    raw = SRC.read_text(encoding="utf-8")
    body = drop_github_nav(raw)
    body = apply_prose_ascii_fallbacks(body)
    body = inject_model_cards(body)
    body = strip_html_comments(body)
    body = drop_composer_appendices(body)
    body = normalize_appendix_headings(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = demote_inventory_headings(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body)
    prune_stale_listings()

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = insert_list_of_figures(latex_body)
    latex_body = insert_appendix_command(latex_body)

    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    preamble = PREAMBLE.read_text(encoding="utf-8")
    title_page = build_title_page(abstract_latex)
    document = build_document(preamble, title_page, latex_body)
    changed = write_if_changed(OUT, document)
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file()) if LISTINGS_DIR.is_dir() else 0
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.pdf"))
    note = "updated" if changed else "unchanged"
    print(
        f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, "
        f"full Lean appendix, {n_listings} listings, "
        f"{n_figures} mermaid figures, {note})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
