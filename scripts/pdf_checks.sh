#!/usr/bin/env bash
# PDF preflight helpers (sourced by build/package scripts).
set -euo pipefail

# Verify every font in a PDF is embedded (emb=yes).
check_pdf_fonts_embedded() {
  local pdf="$1"
  local label="${2:-$pdf}"
  if [[ ! -f "$pdf" ]]; then
    echo "warning: ${label} missing; skipping font-embedding check" >&2
    return 0
  fi
  if ! command -v pdffonts >/dev/null 2>&1; then
    echo "warning: pdffonts not installed; skipping font-embedding check for ${label}" >&2
    return 0
  fi
  local bad
  bad="$(
    pdffonts "$pdf" 2>/dev/null | awk '
      NR > 2 && $0 !~ /^ *$/ && $0 !~ /^name/ && $0 !~ /^----/ && $0 !~ / yes yes / { print }
    '
  )"
  if [[ -n "$bad" ]]; then
    echo "error: ${label} has non-embedded fonts:" >&2
    echo "$bad" | sed 's/^/  /' >&2
    echo "  Rebuild with LuaLaTeX (see .latexmkrc)." >&2
    return 1
  fi
  local count
  count="$(
    pdffonts "$pdf" 2>/dev/null | awk '
      NR > 2 && $0 !~ /^ *$/ && $0 !~ /^name/ && $0 !~ /^----/ && $0 ~ / yes yes / { c++ }
      END { print c+0 }
    '
  )"
  echo "  ${label}: all ${count} font(s) embedded (emb=yes)"
}
