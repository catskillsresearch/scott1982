#!/usr/bin/env bash
# Regenerate arxiv.tex from arxiv.md and compile arxiv.pdf in one shot.
# Lean Code appendix = GitHub hyperlinks + plain URLs (no inlined sources).
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="arxiv.pdf"

# shellcheck source=scripts/arxiv_pdf_checks.sh
source "$(dirname "$0")/arxiv_pdf_checks.sh"

pdf_valid() {
  local f="$1"
  [[ -f "$f" ]] || return 1
  pdfinfo "$f" >/dev/null 2>&1 || return 1
  local pages
  pages="$(pdfinfo "$f" 2>/dev/null | awk '/^Pages:/ {print $2}')"
  [[ -n "$pages" && "$pages" -gt 0 ]]
}

compile_tex() {
  local target="$1"
  local clean="${2:-0}"
  if [[ "$clean" -eq 1 ]]; then
    latexmk -C "$target" >/dev/null 2>&1 || true
    rm -f "${target%.tex}.aux" "${target%.tex}.out" "${target%.tex}.toc" "${target%.tex}.lof"
  fi
  latexmk -interaction=nonstopmode -halt-on-error "$target" >/dev/null 2>&1 || {
    echo "latexmk reported errors compiling ${target}; tail of log:" >&2
    tail -n 40 "${target%.tex}.log" >&2 || true
    exit 1
  }
}

echo "==> Regenerating arxiv.tex + figures/ from arxiv.md"
if [[ "${1:-}" == "--pdf-only" ]]; then
  echo "    (--pdf-only: skipping markdown/tex regeneration)"
else
  bash scripts/build_arxiv_tex.sh
fi

echo "==> Compiling arxiv.pdf (single-shot LuaLaTeX; see .latexmkrc)"
need_main=1
if pdf_valid "$PDF" \
  && [[ ! "$TEX" -nt "$PDF" ]] \
  && [[ ! figures -nt "$PDF" ]]; then
  need_main=0
fi
if [[ "$need_main" -eq 0 ]]; then
  echo "==> Reusing cached $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; arxiv.tex unchanged)"
else
  start_main=$(date +%s)
  main_clean=0
  if ! pdf_valid "$PDF"; then
    main_clean=1
  fi
  compile_tex "$TEX" "$main_clean"
  end_main=$(date +%s)
  main_secs=$((end_main - start_main))
  if ! pdf_valid "$PDF"; then
    echo "error: ${PDF} missing or corrupt after compile" >&2
    exit 1
  fi
  echo "wrote $PDF ($(du -h "$PDF" | cut -f1), $(pdfinfo "$PDF" | awk '/Pages:/ {print $2}') pages; compile ${main_secs}s)"
fi

echo "==> arXiv preflight: font embedding"
check_pdf_fonts_embedded "$PDF" "arxiv.pdf"

echo "==> Packaging arXiv submission zip"
bash scripts/package_arxiv_submit.sh --skip-tex-build
