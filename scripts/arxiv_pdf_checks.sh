#!/usr/bin/env bash
# arXiv preflight checks (sourced by build/package scripts).
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
    echo "error: ${label} has non-embedded fonts (arXiv will reject):" >&2
    echo "$bad" | sed 's/^/  /' >&2
    echo "  Rebuild with a TeX engine that embeds fonts (LuaLaTeX/pdfLaTeX + Latin Modern)." >&2
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

# arXiv upload limit is ~20MB for the submission bundle; flag early if we approach it.
check_submission_size() {
  local zip="$1"
  local zip_bytes
  zip_bytes="$(stat -c%s "$zip")"
  local zip_mb
  zip_mb="$(awk -v b="$zip_bytes" 'BEGIN { printf "%.1f", b/1048576 }')"
  echo "  submission zip: ${zip_mb} MB"
  if [[ "$zip_bytes" -gt 20971520 ]]; then
    echo "error: ${zip} is ${zip_mb} MB (>20 MB arXiv limit)." >&2
    return 1
  fi
  if [[ "$zip_bytes" -gt 15728640 ]]; then
    echo "warning: ${zip} is ${zip_mb} MB (approaching arXiv ~15–20 MB limit)" >&2
  fi
}
