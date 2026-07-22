#!/usr/bin/env bash
# Expand Lean sources into arxiv_with_code.md, then build arxiv.tex + listings/figures.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> Regenerating arxiv_with_code.md (full Lean sources inlined)"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py
